use std::collections::HashSet;
use core::ptr;
use indexmap::IndexMap;
use regex::Regex;
use std::ffi::CStr;
use z3::{
    ast::{Ast, Bool, Dynamic},
    Context,
};
use parser::{
    UnaryOperator, BinOperator,
    AstNode,
};
use ir::EnvState;
use z3_sys::*;


pub fn unrolled_states_from_Z3_ast<'ctx, T: Ast<'ctx>>(
    ast: &T,
    variables: &HashSet<&'ctx str>,
    k: usize
) -> (Vec<EnvState<'ctx>>, Vec<EnvState<'ctx>>) {
    // Create variable mapping
    let mut states: Vec<EnvState<'ctx>> = (0..=k)
        .map(|_| IndexMap::new())
        .collect();
    let mut bounded_vars: Vec<EnvState<'ctx>> = (0..=k)
        .map(|_| IndexMap::new())
        .collect();
    extract_variables_rec(ast, variables, &mut states, &mut bounded_vars);
    (states, bounded_vars)
}

fn extract_variables_rec<'ctx, T: Ast<'ctx>>(
    ast: &T,
    variables: &HashSet<&'ctx str>,
    states: &mut Vec<EnvState<'ctx>>,
    bounded: &mut Vec<EnvState<'ctx>>,
) {
    let states_len = states.len();
    let num_children = ast.children().len();
    for idx in states_len..num_children {
        let node = &ast.children()[idx];
        // The node is an "=". Inspect the left child for probed variables
        // The right child can be used for extracting state variables
        let left_subtree = &node.children()[0];
        let right_subtree = &node.children()[1];
        
        // Handle probed variables
        let child_name = left_subtree.decl().name();
        let state_idx: usize = child_name
            .rsplit('_') // split from the right
            .next()      // take the last part
            .unwrap()    // safe if you know format is correct
            .parse()     // parse to usize
            .unwrap();   // safe if you know it's valid digits
        let after_prefix = child_name.strip_prefix("probe_").unwrap();
        let (before_part3, _part3) = after_prefix.rsplit_once('_').unwrap();
        let (variable_name_ast, _part2) = before_part3.rsplit_once('_').unwrap();
        if let Some(variable_name) = variables.get(variable_name_ast) {
            states[state_idx].insert(*variable_name, Dynamic::from_ast(right_subtree));
        }

        // Handle state variables
        let node_name: String = right_subtree.decl().name();
        println!("{}", node_name);
        let state = match node_name.as_str() {
            "=" => {
                &right_subtree
                    .children()[0]   // extract
                    .children()[0]  // probed variable name
                    .children()[0]  // state
            }
            _ => &right_subtree.children()[0],    // recursive function name
        };
        let state_name: String = state.decl().name();
        let state_idx: usize = state_name
            .rsplit('_') // split from the right
            .next()      // take the last part
            .unwrap()    // safe if you know format is correct
            .parse()     // parse to usize
            .unwrap();   // safe if you know it's valid digits
        bounded[state_idx].insert("bounded", Dynamic::from_ast(state));
    }
}