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
    extract_variables_rec(ast, variables, &mut states, &mut bounded_vars, 0);
    (states, bounded_vars)
}

fn extract_variables_rec<'ctx, T: Ast<'ctx>>(
    ast: &T,
    variables: &HashSet<&'ctx str>,
    states: &mut Vec<EnvState<'ctx>>,
    bounded: &mut Vec<EnvState<'ctx>>,
    indent: usize,
) {
    let name: String = ast.decl().name();
    if name.starts_with("s_") {
        let state_idx: usize = name
            .rsplit('_') // split from the right
            .next()      // take the last part
            .unwrap()    // safe if you know format is correct
            .parse()     // parse to usize
            .unwrap();   // safe if you know it's valid digits
        bounded[state_idx].insert("bounded", Dynamic::from_ast(ast));
    }
    if name == "=" {
        // Inspect left child
        let child = &ast.children()[0];
        let child_name = child.decl().name();
        if child_name.starts_with("probe_") {
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
                let right_hand_side = &ast.children()[1];
                states[state_idx].insert(*variable_name, Dynamic::from_ast(right_hand_side));
            }
        }
    }
    for child in ast.children() {
        extract_variables_rec(&child, variables, states, bounded, indent + 2);
    }
}

