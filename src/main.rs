#![allow(warnings)]
use std::env;
use std::fs;
use std::mem;
use std::io::{self, Write};
use std::process;
use std::path::PathBuf;
use std::path::Path;
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
    let mut cli = Command::new("HyperQB 2.0")
        .override_usage(
            "\nhyperqb -f <FORMULA> -v <FILE>... -t <TOP_MODULE> -o <SMT2_FILE> -l\n\
            hyperqb -f <FORMULA> -v <FILE>... -t <TOP_MODULE> -o <SMT2_FILE> -k <K> -s <SEM> [-m <B>] [-c] [-q]\n\
            hyperqb -f <FORMULA> -n <FILE>... -l\n\
            hyperqb -f <FORMULA> -n <FILE>... -k <K> -s <SEM> [-m <B>] [-c] [-q]"
        )
        .arg(
            arg!(
                -v --verilog <FILE> "Yosys build file"
            )
            .required(false)
            .num_args(1..)
            .value_parser(value_parser!(PathBuf))
            .requires_all(&["top", "yosys_output"]) // if -v, require -t and -o
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
            .required(false)
            .value_parser(value_parser!(usize))
            .requires("semantics") // if -k, must have -s; -m is optional
            .conflicts_with("loop_conditions") // -k vs -l
        )
        .arg(
            arg!(
                -s --semantics <FILE> "Choice of semantics (pes, opt, hpes, hopt)"
            )
            .required(false)
            .value_parser(value_parser!(String))
            .conflicts_with("loop_conditions") // -s not with -l
        )
        .arg(
            arg!(
                -c --counterexample "Generates counterexample if formula is unsat"
            )
            .required(false)
            .conflicts_with("loop_conditions") // -c only in unroll mode
        )
        .arg(
            arg!(
                -l --loop_conditions "Use loop conditions instead of unrolling"
            )
            .required(false)
            .action(clap::ArgAction::SetTrue)
            .conflicts_with_all(&["unrolling_bound","semantics","trajectory_bound","counterexample","qbf_solver"])
        )
        .arg(
            arg!(
                -m --trajectory_bound <FILE> "Trajectory bound"
            )
            .required(false)
            .value_parser(value_parser!(usize))
            .conflicts_with("loop_conditions") // -m only in unroll mode
        )
        .arg(
            arg!(
                -q --qbf_solver "Use QBF solver (default is Z3)"
            )
            .required(false)
            .conflicts_with("loop_conditions") // -q only in unroll mode
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
        .group(
            ArgGroup::new("input")
                .args(["verilog", "nusmv"])
                .required(true)
                .multiple(false)
        )
        // exactly one mode: either -l OR -k (and -k implies -s via requires above)
        .group(
            ArgGroup::new("mode")
                .args(["loop_conditions", "unrolling_bound"])
                .required(true)
                .multiple(false)
        );
    let matches = cli.get_matches();
    let use_loop_conditions = matches.get_flag("loop_conditions");
    let mut unrolling_bound : usize = 0;
    let mut semantics_as_str = &String::from("");
    let mut semantics = Semantics::Pes;
    if !use_loop_conditions {
        unrolling_bound = *matches
            .get_one::<usize>("unrolling_bound")
            .expect("Unrolling bound (-k) is required when not using loop conditions (-l)");
        
        semantics_as_str = matches
            .get_one::<String>("semantics")
            .expect("Semantics (-s) is required when not using loop conditions (-l)");
        
        semantics = match semantics_as_str.as_str() {
            "pes" => Semantics::Pes,
            "opt" => Semantics::Opt,
            "hpes" => Semantics::Hopt,
            "hopt" => Semantics::Hpes,
            _ => panic!("Invalid choice of semantics")
        };
        
    }
    let trajectory_bound = matches
        .get_one::<usize>("trajectory_bound");

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

        let formula = fs::read_to_string(formula_path).expect("Failed to read the formula");
        let mut ast_node = parse(&formula).expect("Failed parsing the formula");
        if *matches.get_one::<bool>("qbf_solver").unwrap() {
            let mut cfg = Config::new();
            cfg.set_model_generation(true);
            let ctx = Context::new(&cfg);
            let mut envs = Vec::new();

            let path_identifiers: Vec<&str> = get_path_identifiers(&ast_node);
            if model_paths.len() != path_identifiers.len() {
                panic!("ERROR: number of provided models and number of path quantifiers do not match!");
            }

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


            let semantics = "hpes"; // temp, not sure what's wrong
            gen_qcir(&envs, &model_paths, &formula, unrolling_bound, false, semantics, Path::new("_outfiles/HQ.qcir"));

            let output = process::Command::new("./quabs")
                .arg("--partial-assignment")
                .arg("_outfiles/HQ.qcir")
                .stdout(process::Stdio::piped())
                .stderr(process::Stdio::piped())
                .spawn()
                .expect("Failed to execute QuAbs, please check QuABs")
                .wait_with_output()
                .expect("Failed to capture QuAbs output");
            
            // Convert stdout and stderr from bytes to string
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            if !stderr.trim().is_empty() {
                println!("{}", stderr);
            }

            let secs = start.elapsed().as_secs_f64();

            let out_path = "_outfiles/quabs.out";
            {
                let mut file = fs::File::create(out_path).expect("Cannot create quabs.out");
                file.write_all(&output.stdout).expect("Failed to write QuAbs output");
            }
            
            let quabs_output = String::from_utf8_lossy(&output.stdout);
            let status = if quabs_output.contains("r UNSAT") {
                "UNSAT"
            } else if quabs_output.contains("r SAT") {
                "SAT"
            } else {
                "UNKNOWN"
            };

            
            println!("QBF Build & Solving Time: {:.3} s", secs);
            println!("{}", status);

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
                let mut lp = LoopCondition::new(&ctx, &envs[0], &envs[1]);
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

        // Get propositions by path
        let propositions = get_propositions_by_path(&ast_node);

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
            // parse the smv for this model
            let env = build_smvenv_from_verilog(
                build_paths[i], 
                top_module, 
                yosys_out,
                &ctx
            ).unwrap();
            envs.push(env);
        }
        let duration = start.elapsed();
        let secs = duration.as_secs_f64();
        println!("Model Creation Time: {}", secs);

        // Start the timer for encoding
        let start = Instant::now();

        let encoding = if *matches.get_one::<bool>("loop_conditions").unwrap() {
            let mut lp = LoopCondition::new(&ctx, &envs[0], &envs[1]);
            lp.build_loop_condition(&ast_node)

        } else {
            get_z3_encoding(&envs, &ast_node, unrolling_bound, trajectory_bound.copied(), semantics, witness)
        };
        
        //println!("{:#?}", encoding);

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