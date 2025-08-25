#![allow(warnings)]
use std::fs;
use std::mem;
use std::io::{self, Write};
use std::process;
use std::path::PathBuf;
use std::time::Instant;
use ir::*;
use parser::*;
use enchelper::*;
use encoder::*;
use parser_nusmv::*;
use unroller_qbf::*;
use loop_conditions::*;
use hqb_verilog::*;
use z3::{
    ast::{
        Ast, Dynamic, Int, Bool,
        BV,
    },
    Config, Context, Solver, SatResult,
    StatisticsValue,
};
use clap::{arg, value_parser, ArgGroup, Command};

fn main() {

    //clap setup
    let cli = Command::new("hyperqb")
        .arg(
            arg!(
                -v --verilog <FILE> "Yosys build file"
            )
            .required(false)
            .num_args(1..)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -n --nusmv <FILE> "NuSMV"
            )
            .required(false)
            .num_args(1..)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -f --formula <FILE> "Hyperproperty formula"
            )
            .required(true)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -k --unrolling_bound <FILE> "Unrolling bound"
            )
            .required(false)  // Changed from true to false
            .value_parser(value_parser!(usize)),
        )
        .arg(
            arg!(
                -s --semantics <FILE> "Choice of semantics"
            )
            .required(false)  // Changed from true to false
            .value_parser(value_parser!(String)),
        )
        .arg(
            arg!(
                -c --counterexample "Generates counterexample if formula is unsat"
            )
            .required(false)
        )
        .arg(
            arg!(
                -l --loop_conditions "Use loop conditions instead of unrolling"
            )
            .required(false)
        )
        .arg(
            arg!(
                -m --trajectory_bound <FILE> "Trajectory bound"
            )
            .required(false)
            .value_parser(value_parser!(usize)),
        )
        .arg(
            arg!(
                -q --qbf_solver "Use QBF solver (default is Z3)"
            )
            .required(false)
        )
        .arg(
            arg!(
                -t --top <TOP_MODULE> "Top module name (default: main)"
            )
            .required(false)
            .default_value("main")
            .value_parser(value_parser!(String)),
        )
        .arg(
            arg!(
                -o --yosys_output <SMT2_FILE> "Location of SMT2 file if using a build file"
            )
            .required(false)
            .value_parser(value_parser!(PathBuf)),
        )
        .group(ArgGroup::new("input")
            .args(["verilog", "nusmv"])
            .required(true)
            .multiple(false)
        );
        // .group(ArgGroup::new("verilog-branch")
        //     .args(["top", "yosys_output"])
        //     .requires("verilog")
        // );

    let matches = cli.get_matches();

    let mut unrolling_bound = *matches
        .get_one::<usize>("unrolling_bound")
        .expect("Unrolling bound (-k) is required when not using loop conditions (-l)");

    let semantics_as_str = matches
        .get_one::<String>("semantics")
        .expect("Semantics (-s) is required when not using loop conditions (-l)");

    let mut semantics = match semantics_as_str.as_str() {
        "pes" => Semantics::Pes,
        "opt" => Semantics::Opt,
        "hpes" => Semantics::Hopt,
        "hopt" => Semantics::Hpes,
        _ => panic!("Invalid choice of semantics")
    };

    // Check if loop conditions flag is set
    if *matches.get_one::<bool>("loop_conditions").unwrap() {
        unrolling_bound = 0;
        semantics = Semantics::Pes;
    }

    let formula_path = matches
        .get_one::<PathBuf>("formula").unwrap();

    if let Some(nusmv_models) = matches.get_many::<PathBuf>("nusmv") {
        // NuSMV Path
        let model_paths: Vec<_> = nusmv_models.cloned().collect();
        let model_paths: Vec<&str> = model_paths
            .iter()
            .map(|p| {
                p.to_str()
                .expect("Path is not valid UTF-8")
            })
            .collect();
        
        let trajectory_bound = matches
            .get_one::<usize>("trajectory_bound");

        let formula = fs::read_to_string(formula_path).expect("Failed to read the formula");
        let mut ast_node = parse(&formula).expect("Failed parsing the formula");
        if *matches.get_one::<bool>("qbf_solver").unwrap() {
            
            let mut cfg = Config::new();
            cfg.set_model_generation(true);
            let ctx = Context::new(&cfg);
            
            gen_qcir(&ctx, &model_paths, &String::from(formula_path.to_str().unwrap()), unrolling_bound as i32, false, semantics_as_str);
            let output = process::Command::new("/Users/milad/Desktop/rust_tutorial/HyperRUSTY/quabs")
                .arg("outputs/HQ.qcir")
                .stdout(process::Stdio::piped())
                .spawn()
                .expect("QuAbs can not be executed")
                .wait_with_output().expect("QuAbs output is problematic.");
            
            // Convert stdout and stderr from bytes to string
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            // Print based on success or failure
            if !stdout.trim().is_empty() {
                println!("{}", stdout);
            }
            if !stderr.trim().is_empty() {
                println!("{}", stderr);
            }
        } else {
            // Should we use the negation for counterexample generation?
            let mut witness : bool = false;
            if *matches.get_one::<bool>("counterexample").unwrap() {
                witness = true;
                ast_node = negate_formula(&ast_node);
            }

            let path_identifiers: Vec<&str> = get_path_identifiers(&ast_node);

            if model_paths.len() != path_identifiers.len() {
                panic!("ERROR: number of provided models and number of path quantifiers do not match!");
            }

            let mut cfg = Config::new();
            cfg.set_model_generation(true);
            let ctx = Context::new(&cfg);
            let mut envs = Vec::new();

            // Start the timer for model parsing
            let start = Instant::now();

            for i in 0..path_identifiers.len() {
                // parse the smv for this model
                let env = parse_smv(
                    &ctx,
                    model_paths[i],
                    Some("output.txt".to_string()),
                    false,
                    "model",
                    "ir",
                );
                envs.push(env);
            }
            let duration = start.elapsed();
            let secs = duration.as_secs_f64();
            println!("Model Creation Time: {}", secs);

            // Start the timer for encoding
            let start = Instant::now();
            let encoding = if *matches.get_one::<bool>("loop_conditions").unwrap() {
                let lp = LoopCondition::new(&ctx, &envs[0], &envs[1]);
                lp.build_loop_condition(&ast_node)

            } else {
                get_z3_encoding(&envs, &ast_node, unrolling_bound, trajectory_bound.copied(), semantics, witness)
            };
            let duration = start.elapsed();
            let secs = duration.as_secs_f64();
            println!("Encoding Time: {}", secs);

            // Create a new solver
            let solver = Solver::new(&ctx);
            solver.assert(&encoding);
            match solver.check() {
                SatResult::Sat => {
                    // Is counterexample set?
                    if witness {
                        println!("result: unsat.");
                        let model = solver.get_model().unwrap();
                        let grouped = extract_grouped_model(&model);
                        for (state, entries) in grouped {
                            println!("\nState {state}:");
                            for (var, val) in entries {
                                println!("  {var} = {val}");
                            }
                        }

                    }else {
                        println!("result: sat.");
                    }
                },
                SatResult::Unsat => {
                    if witness {
                        println!("result: sat.");
                    }else {
                        println!("result: unsat.");
                    }
                },
                SatResult::Unknown => {
                    println!("result: unknown.");
                }
            };
            // grab the statistics of the solver
            let stats = solver.get_statistics();
            let val_str = match stats.value("time").unwrap() {
                StatisticsValue::UInt(u)   => u.to_string(),
                StatisticsValue::Double(d) => d.to_string(),
            };
            println!("Solve Time: {}", val_str);
        }
    } else {
        // Verilog Path
        // TODO: Duplicate code. Needs to be managed
        let build_paths: Vec<_> = matches
            .get_many::<PathBuf>("verilog")
            .unwrap()
            .map(|pb| pb.as_path())
            .collect();


        // Top module
        let top_module = matches
            .get_one::<String>("top")
            .expect("Top module name (-t) is required when using verilog (-v, --verilog)");

        // Yosys output file
        let yosys_out = matches
            .get_one::<PathBuf>("yosys_output")
            .expect("Yosys output file name (-o) is required when using verilog (-v, --verilog)")
            .as_path();
        
        let formula = fs::read_to_string(formula_path).expect("Failed to read the formula");
        let mut ast_node = parse(&formula).expect("Failed parsing the formula");

        // Should we use the negation for counterexample generation?
        let mut witness : bool = false;
        if *matches.get_one::<bool>("counterexample").unwrap() {
            witness = true;
            ast_node = negate_formula(&ast_node);
        }

        // Check if the number of models and quantifiers match
        let path_identifiers: Vec<&str> = get_path_identifiers(&ast_node);
        if build_paths.len() != path_identifiers.len() {
            panic!("ERROR: number of provided models and number of path quantifiers do not match!");
        }

        let mut cfg = Config::new();
        cfg.set_model_generation(true);
        let ctx = Context::new(&cfg);
        let mut envs = Vec::new();

        // Start the timer for model parsing
        // Can you the path_identifiers variable above to annotate models
        let start = Instant::now();

        // Call Verilog-related code to obtain SMT2-LIB outputs
        let mut models: Vec<String> = Vec::with_capacity(path_identifiers.len());

        for i in 0..path_identifiers.len() {
            // Create fake environments for compatibility
            let env = SMVEnv::new(&ctx);
            envs.push(env);
            // Get SMT2-LIB from each build file
            let smt2_model = match unroll_from_smt_build(build_paths[i], top_module, yosys_out, unrolling_bound, path_identifiers[i]) {
                Ok((unrolled, a1, a2)) => {
                    println!("{:#?}", a2);
                    unrolled
                },
                Err(e) => panic!("{}", e),
            };
            models.push(smt2_model);
        }
        let duration = start.elapsed();
        let secs = duration.as_secs_f64();
        println!("Model Creation Time: {}", secs);

        // Start the timer for encoding
        let start = Instant::now();

        let encoding = get_verilog_encoding(&envs, &models, &ast_node, unrolling_bound, semantics, witness);
        
        let duration = start.elapsed();
        let secs = duration.as_secs_f64();
        println!("Encoding Time: {}", secs);

        // Create a new solver
        let solver = Solver::new(&ctx);
        solver.assert(&encoding);

        match solver.check() {
            SatResult::Sat => {
                // Is counterexample set?
                if witness {
                    println!("result: unsat.");
                    let model = solver.get_model().unwrap();
                    let grouped = extract_grouped_model(&model);
                    for (state, entries) in grouped {
                        println!("\nState {state}:");
                        for (var, val) in entries {
                            println!("  {var} = {val}");
                        }
                    }

                }else {
                    println!("result: sat.");
                }
            },
            SatResult::Unsat => {
                if witness {
                    println!("result: sat.");
                }else {
                    println!("result: unsat.");
                }
            },
            SatResult::Unknown => {
                println!("result: unknown.");
            }
        };
        // grab the statistics of the solver
        let stats = solver.get_statistics();
        let val_str = match stats.value("time").unwrap() {
            StatisticsValue::UInt(u)   => u.to_string(),
            StatisticsValue::Double(d) => d.to_string(),
        };
        println!("Solve Time: {}", val_str);
    }

}