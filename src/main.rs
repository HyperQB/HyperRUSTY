#![allow(warnings)]
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
                -l --loop_conditions "Use loop conditions instead of unrolling"
            )
            .required(false)
            .action(clap::ArgAction::SetTrue),
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

    // Check if loop conditions flag is set
    let use_loop_conditions = matches.get_flag("loop_conditions");

    // Handle conditional requirements
    let (unrolling_bound, semantics) = if use_loop_conditions {
        // When using loop conditions, we don't need unrolling bound or semantics
        (0, Semantics::Pes) // Default values (not used)
    } else {
        // When NOT using loop conditions, both unrolling bound and semantics are required
        let unrolling_bound = matches
            .get_one::<usize>("unrolling_bound")
            .expect("Unrolling bound (-k) is required when not using loop conditions (-l)");

        let semantics_as_str = matches
            .get_one::<String>("semantics")
            .expect("Semantics (-s) is required when not using loop conditions (-l)");

        let semantics = match semantics_as_str.as_str() {
            "pes" => Semantics::Pes,
            "opt" => Semantics::Opt,
            "hpes" => Semantics::Hopt,
            "hopt" => Semantics::Hpes,
            _ => panic!("Invalid choice of semantics")
        };

        (*unrolling_bound, semantics)
    };

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

        // To be replaced with the formula path
        let formula = fs::read_to_string(formula_path).expect("Failed to read the formula");
        let ast_node = parse(&formula).expect("Failed parsing the formula");

        if *matches.get_one::<bool>("qbf_solver").unwrap() {
            // QBF unrolling

            // create ENV
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
            gen_qcir(&envs, &model_paths, &formula, unrolling_bound, false, semantics, Path::new("outputs/HQ.qcir"));

            let output = process::Command::new("./quabs")
                .arg("--partial-assignment")
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

            let duration = start.elapsed();
            let secs = duration.as_secs_f64();
            println!("QBF Build & Solving Time: {}", secs);
        } else {
            let path_identifiers: Vec<&str> = get_path_identifiers(&ast_node);

            let mut cfg = Config::new();
            cfg.set_model_generation(true);
            let ctx = Context::new(&cfg);
            let mut envs = Vec::new();

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

            let encoding = if use_loop_conditions {
                let lp = LoopCondition::new(&ctx, &envs[0], &envs[1]);
                lp.build_loop_condition(&ast_node)

            } else {
                get_z3_encoding(&envs, &ast_node, unrolling_bound, None, semantics)
            };
            let duration = start.elapsed();
            let secs = duration.as_secs_f64();
            println!("Encoding Time: {}", secs);

            // Create a new solver
            let solver = Solver::new(&ctx);
            solver.assert(&encoding);

            match solver.check() {
                SatResult::Sat => {
                    println!("result: sat.");
                },
                SatResult::Unsat => {
                    println!("result: unsat.");
                },
                SatResult::Unknown => {
                    println!("result: unknown.");
                }
            };
            // grab the statistics of the solver
            // let stats = solver.get_statistics();
            // let val_str = match stats.value("time").unwrap() {
            //     StatisticsValue::UInt(u)   => u.to_string(),
            //     StatisticsValue::Double(d) => d.to_string(),
            // };
            // println!("Solve Time: {}", val_str);
        }
    } else {
        // Verilog Path
        panic!("I Shouldn't be here! -Said verilog");
        let build_path = matches
            .get_one::<PathBuf>("verilog").unwrap();

        let output_file = matches
            .get_one::<PathBuf>("yosys_output").unwrap();

        let top_module = matches
            .get_one::<String>("top").unwrap();
    }

}