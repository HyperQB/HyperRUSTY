#![allow(warnings)]
use std::fs;
use ir::*;
use parser::*;
use enchelper::*;
use encoder::*;
use z3::{
    ast::{
        Ast, Dynamic, Int, Bool,
        BV,
    },
    Config, Context, Solver, SatResult,
};
use clap::{arg, value_parser, ArgGroup, Command};

fn main() {

    //clap setup
    let cli = Command::new("hqb-verilog")
        .arg(
            arg!(
                -v --verilog <FILE> "Input file"
            )
            .required(false)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -n --nusmv <FILE> "Input file"
            )
            .required(false)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -t --top <TOP_MODULE> "Top module name (default: main)"
            )
            .required(true)
            .default_value("main")
            .value_parser(value_parser!(String)),
        )
        .arg(
            arg!(
                -s --smt2_path <SMT2_FILE> "Location of SMT2 file if using a build file"
            )
            .required(false)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -b --build <BUILD_FILE> "Yosys build file"
            )
            .required(false)
            .value_parser(value_parser!(PathBuf)),
        )
        .arg(
            arg!(
                -u --unroll <BOUND> "Unroll the design directly from the smt2 file up to bound"
            )
            .value_parser(value_parser!(u32))
            .required(true)  
        )
        .arg(
            arg!(
                -i --trace_id <TRACE_ID> "Trace ID for unrolling"
            )
            .value_parser(value_parser!(String))
            .required(true)
        )
        .group(ArgGroup::new("input")
            .args(["verilog", "build"])
            .required(true)
        );





    // // Bring in the source
    // let source = fs::read_to_string("formula.hq").expect("Failed to read source");

    // let ast_node = parse(&source).expect("Input parsing failed");

    // let mut cfg = Config::new();
    // cfg.set_model_generation(true);
    // let ctx = Context::new(&cfg);
    // let solver = Solver::new(&ctx);

    // let mut env = SMVEnv::new(&ctx);

    // env.register_variable("high", VarType::Bool {init: Some(vec![false])});
    // env.register_variable("low", VarType::Bool {init: Some(vec![false])});
    // env.register_variable("halt", VarType::Bool {init: Some(vec![false])});
    // env.register_variable("pc", VarType::Int {init: Some(vec![1]), lower: Some(1), upper: Some(5)});

    // // Transitions
    // env.register_transition("high",
    // |_env, _ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 1))),
    // |_env, _ctx, _state| choice!(Bool, true, false)
    // );

    // env.register_transition("low",
    // |_env, _ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 2))),
    // |_env, _ctx, _state| exact!(Bool, false)
    // );
    // env.register_transition("low",
    // |_env, _ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 4))),
    // |_env, _ctx, _state| exact!(Bool, true)
    // );

    // env.register_transition("pc",
    // |_env, _ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 1))),
    // |_env, _ctx, _state| exact!(Int, 2)
    // );
    // env.register_transition("pc",
    // |_env, _ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 2))),
    // |_env, _ctx, _state| exact!(Int, 3)
    // );
    // env.register_transition("pc",
    // |_env, _ctx, _state| exact!(Node, bool_var!(_state, "high") & int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 3))),
    // |_env, _ctx, _state| exact!(Int, 4)
    // );
    // env.register_transition("pc",
    // |_env, _ctx, _state| exact!(Node, !bool_var!(_state, "high") & int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 3))),
    // |_env, _ctx, _state| exact!(Int, 5)
    // );
    // env.register_transition("pc",
    // |_env, _ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 5))),
    // |_env, _ctx, _state| exact!(Int, 5)
    // );

    // env.register_transition("halt",
    // |_env, _ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 5))),
    // |_env, _ctx, _state| exact!(Bool, true)
    // );

    // env.register_transition("halt",
    // |_env, _ctx, _state| exact!(Node, predicate!("halt", _env, _ctx, _state)),
    // |_env, _ctx, _state| exact!(Bool, true)
    // );

    // env.register_predicate("halt",
    // |_env, _ctx, _state| int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 5))
    // );

    // let K: usize = 5;
    // let M: usize = 5;

    // let (states_a, sym_path_a) = env.generate_symbolic_path(K, Some("A"));
    // let (states_b, sym_path_b) = env.generate_symbolic_path(K, Some("B"));

    // let form = get_z3_encoding(&env, &ast_node, K, Some(M), Semantics::Hpes);

    // solver.assert(&form);

    // match solver.check() {
    //     SatResult::Sat => {
    //         println!("result: sat.");
    //     },
    //     SatResult::Unsat => {
    //         println!("result: unsat.");
    //     },
    //     SatResult::Unknown => {
    //         println!("result: unknown.");
    //     }
    // };

}