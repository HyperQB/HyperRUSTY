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
    let name: String = ast.decl().name();
    if let Some(name_ref) = variables.get(name.as_str()) {
        let child = &ast.children()[0];
        let child_name = child.decl().name();
        let state_idx: usize = child_name
            .rsplit('_') // split from the right
            .next()      // take the last part
            .unwrap()    // safe if you know format is correct
            .parse()     // parse to usize
            .unwrap();   // safe if you know it's valid digits
        states[state_idx].insert(name_ref, Dynamic::from_ast(ast));
        bounded[state_idx].insert("bounded", Dynamic::from_ast(child));
    }
    for child in ast.children() {
        extract_variables_rec(&child, variables, states, bounded);
    }
}