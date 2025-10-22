#![allow(dead_code, unused, warnings)] // Allow warnings for dead code and unused things

extern crate expressions;
use std::{env, fs};
use expressions::*;
extern crate fsm;

// Stuff for timing
use std::time::{Duration, Instant};
use std::thread::sleep;

// stuff for nusmv
use std::fs::File;
use std::io::{self, Write};
use std::process::{Command, Stdio};
use std::path::Path;

use std::error::Error;
use std::io::{BufReader, BufRead};

use z3::{ast::{Dynamic, Ast}};
use z3::{Config, Context, ast::{Bool, Int}};
use ir::{SMVEnv, VarType, Variable, ReturnType, EnvState};
use ir::*;
use std::process::exit;
use std::collections::HashSet;

// use crate::utils::*;
use crate::utils::replace_last_occurrence;

// use library flags
use flags::FLAGS;
use flags::flags::parse_flags;

// some utility functions
mod utils;

// use library parser_nusmv
use parser_nusmv::parse_smv;

// use library unroller_qbf
use unroller_qbf::gen_qcir;



// DEBUG: manually create SMVEnv
fn create_env<'ctx>(ctx: &'ctx Context) -> SMVEnv<'ctx> {
    let mut env = SMVEnv::new(ctx);

    // Register a Bool variable
    env.register_variable("x", VarType::Bool {
        init: Some(vec![true]),
    });

    // Register an Int variable
    env.register_variable("y", VarType::Int {
        init:   Some(vec![1]),
        lower:  Some(0),
        upper:  Some(1),
    });

    // // Register a predicate: y reaches 5
    // env.register_predicate("is_y_eq_5", 
    //     |_ctx, _state| exact!(Node, int_var!(_state, "y")._eq(&Int::from_i64(_ctx, 5)))
    // );
    env.register_transition("x",
        |_ctx, _state| exact!(Node, bool_var!(_state, "x")),
        |_ctx, _state| exact!(Node, !bool_var!(_state, "x"))
    );

    // Register a transition for "y": if x is true, y becomes y+1
    env.register_transition("y",
        |_ctx, _state| exact!(Node, bool_var!(_state, "x")),
        |_ctx, _state| exact!(Node, int_var!(_state, "y") + 1i64)
    );
    // Register a transition for "y": if x is false, y becomes y-1
    env.register_transition("y",
        |_ctx, _state| exact!(Node, !bool_var!(_state, "x")),
        |_ctx, _state| exact!(Node, int_var!(_state, "y") - 1i64)
    );

    env
}


fn main() {
    // =========================================
    // Get the args
    // \TBD: Integrate this part with main.rs
    let logger = flags::parse_flags();
    let mut args = env::args().skip(1); // Skip program name
    let mut files: Vec<String> = args
        .by_ref()
        .take_while(|arg| !arg.starts_with('-'))
        .collect();
    // println!("Files: {:?}", files);
    let formula_file = files.pop().expect("Expected at least one input file");
    let cwd = env::current_dir().expect("Failed to get current directory");
    let path_string = cwd.display().to_string();
    let layers = FLAGS.layers;
    let debug = FLAGS.debug;
    let semantics = FLAGS.sem.clone();
    let now = Instant::now();
    // sanity check
    if files.len() < 2 {
        panic!("Must enter at least two smv files");
    }

    // =========================================
    // NuSMV parser
    // \TBD: Integrate this part with main.rs
    // println!("Parsing NuSMV in IR\n");
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let input_path = "cases/mini/mini.smv";
    let output_path = Some("output.txt".to_string());
    let bit_encode = false;
    let input_format = "model";
    // let output_format = "functions";
    let output_format = "ir"; // --> set format as ir

    // here we get an SMVEnv from the arguments
    let env = parse_smv(
        input_path,
        output_path,
        bit_encode,
        input_format,
        output_format,
    );
    
    // DEBUG: check the registered NuSMV
    // let env = create_env(&ctx); // <-- DEBUG: you can manually create env
    // let state_vars: Vec<EnvState> = env.generate_state_variables(1, None);
    // let constraints = env.generate_bound_constraints(&state_vars);
    // let init_constraints = env.generate_initial_constraints(&state_vars);
    // for (i, constraint) in init_constraints.iter().enumerate() {
    //     println!("\nInitial constraint {}: {}", i, constraint);
    // }
    let time1 = now.elapsed().as_micros();
    // println!("> NuSMV parse finished: {} s \n", time1 as f64 / 1_000_000.0);
    

    // =========================================
    // Given a SMVEnv, unroll models with formula, output a QCIR
    // println!("\nQBF unrolling Starts!\n");

    gen_qcir(&mut files, &formula_file, &env, layers, debug, &semantics);


    // print time elapsed
    let time2 = now.elapsed().as_micros();
    // println!("> Rust genqbf finished: {} s \n", time2 as f64 / 1_000_000.0);
    // println!("> TOTAL: {} s \n", (time1+time2) as f64 / 1_000_000.0);
    // println!("HyperRust finished.\n");

}


