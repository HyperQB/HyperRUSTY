#![allow(warnings)]
use std::fs;
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
            .required(true)
            .value_parser(value_parser!(usize)),
        )
        .arg(
            arg!(
                -s --semantics <FILE> "Choice of semantics"
            )
            .required(true)
            .value_parser(value_parser!(String)),
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

    let unrolling_bound = matches
        .get_one::<usize>("unrolling_bound").unwrap();

    let formula_path = matches
        .get_one::<PathBuf>("formula").unwrap();

    let semantics_as_str = matches.get_one::<String>("semantics").unwrap().as_str();

    let semantics = match semantics_as_str {
            "pes" => Semantics::Pes,
            "opt" => Semantics::Opt,
            "hpes" => Semantics::Hopt,
            "hopt" => Semantics::Hpes,
            _ => panic!("Invalid choice of semantics")
        };

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

        println!("{:?}", ast_node);

        let mut cfg = Config::new();
        cfg.set_model_generation(true);
        let ctx = Context::new(&cfg);

        if *matches.get_one::<bool>("qbf_solver").unwrap() {
            // gen_qcir(&model_paths, &String::from(formula_path.to_str().unwrap()), &env, *unrolling_bound as i32, false, semantics_as_str);
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
        }else {
            let path_identifiers: Vec<&str> = get_path_identifiers(&ast_node);
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
            let form = get_z3_encoding(&envs, &ast_node, *unrolling_bound, None, semantics);
            let duration = start.elapsed();
            let secs = duration.as_secs_f64();
            println!("Encoding Time: {}", secs);


            // Create a new solver
            let solver = Solver::new(&ctx);
            solver.assert(&form);

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
            let stats = solver.get_statistics();
            let val_str = match stats.value("time").unwrap() {
                StatisticsValue::UInt(u)   => u.to_string(),
                StatisticsValue::Double(d) => d.to_string(),
            };
            println!("Solve Time: {}", val_str);
        }

        
    }else {
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