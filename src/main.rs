#![allow(warnings)]
use std::fs;
use std::path::PathBuf;
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
        .arg(
            arg!(
                -b --build <BUILD_FILE> "Yosys build file"
            )
            .required(false)
            .value_parser(value_parser!(PathBuf)),
        )
        .group(ArgGroup::new("input")
            .args(["verilog", "nusmv"])
            .required(true)
            .multiple(false)
        );

        let matches = cli.get_matches();

        let paths: Vec<PathBuf> = matches
            .get_many::<PathBuf>("nusmv").unwrap().cloned().collect();

        for path in paths {
            println!("{:?}", path);
        }





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