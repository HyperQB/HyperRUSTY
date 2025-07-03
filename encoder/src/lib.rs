use std::collections::HashMap;
use z3::{
    ast::{
        Ast, Bool, Dynamic, 
        forall_const, exists_const,
    },
    Context,
};
use enchelper::{Semantics, create_path_mapping};
use ir::*;
use hltlunroller::*;
use ahltlunroller::*;
use parser::*;

// Combines the LTL encoding of the formula with valid path conditions
fn generate_inner_encoding<'ctx>(ctx: &'ctx Context, formula: &AstNode, path_encodings: &Vec<&Bool<'ctx>>, inner_ltl: Bool<'ctx>, k: usize) -> Bool<'ctx> {
    match formula {
        AstNode::HAQuantifier {form, ..} => path_encodings[k].implies(&generate_inner_encoding(ctx, form, path_encodings, inner_ltl, k + 1)),
        AstNode::HEQuantifier {form, ..} => Bool::and(ctx, &[&path_encodings[k], &generate_inner_encoding(ctx, form, path_encodings, inner_ltl, k + 1)]),
        _ => inner_ltl
    }
}

fn generate_quantified_encoding<'ctx>(ctx: &'ctx Context, formula: &AstNode, paths: &Vec<&Vec<EnvState<'ctx>>>, path_encodings: &Vec<&Bool<'ctx>>, mapping: &HashMap<&str, usize>, inner: Bool<'ctx>) -> Bool<'ctx> {
    match formula {
        AstNode::HAQuantifier {form, identifier} => {
            let idx = mapping.get(identifier as &str).unwrap();
            let selected_path = paths[*idx];
            let vars: Vec<Dynamic<'ctx>> = selected_path
                .iter()
                .flat_map(|env| env.values().cloned()) // clones Dynamic<'ctx>
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            // Step 2: Convert to a slice
            let ast_slice: &[&dyn Ast<'ctx>] = &ast_refs;
            forall_const(
                ctx,
                ast_slice,
                &[],
                &generate_quantified_encoding(ctx, form, paths, path_encodings, mapping, inner)
            )
        }
        AstNode::HEQuantifier {form, identifier} => {
            let idx = mapping.get(identifier as &str).unwrap();
            let selected_path = paths[*idx];
            let vars: Vec<Dynamic<'ctx>> = selected_path
                .iter()
                .flat_map(|env| env.values().cloned()) // clones Dynamic<'ctx>
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            // Step 2: Convert to a slice
            let ast_slice: &[&dyn Ast<'ctx>] = &ast_refs;
            exists_const(
                ctx,
                ast_slice,
                &[],
                &generate_quantified_encoding(ctx, form, paths, path_encodings, mapping, inner)
            )
        }
        _ => inner
    }
}

pub fn generate_hltl_encoding<'ctx>(ctx: &'ctx Context, formula: &AstNode, paths: &Vec<&Vec<EnvState<'ctx>>>, path_encodings: &Vec<&Bool<'ctx>>, sem: &Semantics) -> Bool<'ctx> {
    // Unroll the formula first
    let inner_ltl = unroll_hltl_formula(ctx, formula, paths, sem);
    // Construct the inner encoding
    let inner = generate_inner_encoding(ctx, formula, path_encodings, inner_ltl.clone(), 0);
    // Get the mapping
    let mapping = create_path_mapping(formula, 0);
    // Build the complete encoding
    generate_quantified_encoding(ctx, formula, paths, path_encodings, &mapping, inner.clone())

}