/// This is the lib file for the Finite State Machine. It contains the definitions for the expressions that the fsm can parse.
///
/// We are given an input such as: ((a)->((a'\/~a')))/\((~a)->(~a'))
/// We have a second input which is initial state like this: a
/// Finally, we have the number of time steps we are running for.
///
/// We need to parse the input into a series of expressions that we can evaluate.
/// If there is an or, we need to create a branching path.
/// We won't evaluate the expression yet, This is just creating the finite state machine and
/// some functions that take the time parameter and return the possible states at that time.
pub mod helper_functions;
mod gate_builder;
mod unroller;
mod input_to_expressions;
mod parser;
mod symbol_map;
mod csv_parser;
mod encoder;
// pub mod ir_parser;

pub use helper_functions::create_file;
pub use unroller::unwrap;
pub use csv_parser::csv_to_expr;
pub use helper_functions::replace_last_occurrence;
pub use parser::*;
pub use symbol_map::*;
pub use gate_builder::*;
pub use unroller::legacy_unwrap;
pub use unroller::encoding_unroll;
// pub use ir_parser::parse_IL;