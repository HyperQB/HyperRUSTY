use z3::{
    Config, Context, SatResult,
    Solver, ast::{Ast, Bool, Int}
};

fn main() {
    // Initial setup
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    // Define constants 
    let x = ast::Bool::from_bool(&ctx, true);
    let y = ast::Bool::from_bool(&ctx, false);

    // Encode: x -> y and y -> x
    let first_const = x.implies(&y);
    let second_const = y.implies(&x);

    // Populate the solver
    solver.assert(&first_const);
    solver.assert(&second_const);

    // Check satisfiability
    match solver.check() {
        SatResult::Sat => {
            println!("result: sat.");
            // get the model from the solver (no error, since it exists)
            let model = solver.get_model().unwrap();
            let value_x: bool = model.eval(&x, false).unwrap().as_bool().unwrap();
            let value_y: bool = model.eval(&y, false).unwrap().as_bool().unwrap();

            println!("x: {value_x}");
            println!("y: {value_y}");
        },
        SatResult::Unsat => {
            println!("result: unsat.");
        },
        SatResult::Unknown => {
            println!("result: unknown.");
        }
    };
}