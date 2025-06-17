#![allow(warnings)]
use std::fs;
use ir::*;
use parser::*;
use unroller::*;
use encoder::*;
use z3::{
    ast::{
        Ast, Dynamic, Int, Bool,
        BV,
    },
    Config, Context, Solver, SatResult,
};

fn main() {

    // Bring in the source
    let source = fs::read_to_string("formula.hq").expect("Failed to read source");

    let ast_node = parse(&source).expect("Input parsing failed");

    let mut cfg = Config::new();
    cfg.set_model_generation(true);
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let mut env = SMVEnv::new(&ctx);

    env.register_variable("high", VarType::Bool {init: Some(vec![false])});
    env.register_variable("low", VarType::Bool {init: Some(vec![false])});
    env.register_variable("halt", VarType::Bool {init: Some(vec![false])});
    env.register_variable("pc", VarType::Int {init: Some(vec![1]), lower: Some(1), upper: Some(5)});

    // Transitions
    env.register_transition("high",
    |_ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 1))),
    |_ctx, _state| choice!(Bool, true, false)
    );

    env.register_transition("low",
    |_ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 2))),
    |_ctx, _state| exact!(Bool, false)
    );
    env.register_transition("low",
    |_ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 4))),
    |_ctx, _state| exact!(Bool, true)
    );

    env.register_transition("pc",
    |_ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 1))),
    |_ctx, _state| exact!(Int, 2)
    );
    env.register_transition("pc",
    |_ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 2))),
    |_ctx, _state| exact!(Int, 3)
    );
    env.register_transition("pc",
    |_ctx, _state| exact!(Node, bool_var!(_state, "high") & int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 3))),
    |_ctx, _state| exact!(Int, 4)
    );
    env.register_transition("pc",
    |_ctx, _state| exact!(Node, !bool_var!(_state, "high") & int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 3))),
    |_ctx, _state| exact!(Int, 5)
    );
    env.register_transition("pc",
    |_ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 5))),
    |_ctx, _state| exact!(Int, 5)
    );

    env.register_transition("halt",
    |_ctx, _state| exact!(Node, int_var!(_state, "pc")._eq(&Int::from_i64(_ctx, 5))),
    |_ctx, _state| exact!(Bool, true)
    );

    let BOUND: usize = 5;

    let (states_a, sym_path_a) = env.generate_symbolic_path(BOUND, Some("A"));
    let (states_b, sym_path_b) = env.generate_symbolic_path(BOUND, Some("B"));

    let form = generate_hltl_encoding(&ctx, &ast_node, &vec![&states_a, &states_b], &vec![&sym_path_a, &sym_path_b], &Semantics::Pes);

    // println!("{:?}", sym_path_a);

    // println!("{:?}", ast_node);

    println!("{:?}", form);

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

}