use std::collections::HashMap;
use ir::*;
use z3::{Context,
    ast::{
        Ast, Dynamic, Bool,
    }
};
use parser::{
    UnaryOperator, BinOperator,
    AstNode,
};

#[derive(Debug, Clone)]
pub enum Semantics {
    Pes,
    Opt,
    Hpes,
    HOpt,
}

enum UnrollingReturn<'ctx> {
    Bool(Bool<'ctx>),
    Var(Dynamic<'ctx>),
}

impl<'ctx> UnrollingReturn<'ctx> {
    pub fn unwrap_bool(self) -> Bool<'ctx> {
        match self {
            UnrollingReturn::Bool(b) => b,
            _ => panic!("Expected UnrollingReturn::Bool type"),
        }
    }
}

// Creates a mapping of the quantified path variables to their corresponding
// index in the state set.
pub fn create_hltl_mapping(formula: &AstNode, k: usize) -> HashMap<&str, usize> {
    let mut mapping = HashMap::<&str, usize>::new();
    match formula {
        AstNode::HAQuantifier{identifier, form} |
        AstNode::HEQuantifier{identifier, form} => {
            // Recursively map inner quantifiers.
            mapping.extend(create_hltl_mapping(form, k + 1));
            // Update mapping
            mapping.insert(identifier, k);
            // Return the result
            mapping
        }
        _ => mapping
    }
}

pub fn unroll_hltl_formula<'ctx>(ctx: &'ctx Context, formula: &AstNode, paths: &Vec<&Vec<EnvState<'ctx>>>, sem: &Semantics) -> Bool<'ctx> {
    // Create a mapping from path quantifiers to the relevent state
    let mapping = create_hltl_mapping(formula, 0);
    // Sanity check
    if paths.len() != mapping.keys().len() {
        panic!("Number of path quantifiers and provided paths must match");
    }

    // Remove all quantifiers.
    let ltl = inner_ltl(formula);
    unroll_ltl_formula(ctx, ltl, paths, &mapping, 0, sem).unwrap_bool()
}

fn inner_ltl(formula: &AstNode) -> &AstNode {
    match formula {
        AstNode::HAQuantifier{identifier: _, form} |
        AstNode::HEQuantifier{identifier: _, form} => {
            inner_ltl(form)
        }
        _ => formula
    }
}

fn is_halted<'ctx>(ctx: &'ctx Context, paths: &Vec<&Vec<EnvState<'ctx>>>) -> Bool<'ctx> {
    // Checks if `halted` holds on the last state of unrolling
    // Get the unrolling bound (states are not empty)
    let bound = paths[0].len() - 1;
    let mut halt_vars = Vec::<Bool<'ctx>>::new();
    for i in 0..paths.len() {
        // Get the mapping corresponding to the last state
        let final_step = &paths[i][bound];
        //Halted is a boolean variable
        // If the state doesn't have `halt`, panic
        let halt = match final_step.get("halt") {
            Some(node) => node,
            None => panic!("`halt` is not defined on model number {}", i + 1)
        };
        // It's a dynamic variable, so it needs to be cast as a Boolean
        halt_vars.push(halt.as_bool().unwrap());
    }
    let refs: Vec<&Bool> = halt_vars.iter().collect();
    Bool::and(ctx, &refs)
}

fn unroll_ltl_formula<'ctx>(ctx: &'ctx Context, formula: &AstNode, paths: &Vec<&Vec<EnvState<'ctx>>>, mapping: &HashMap<&str, usize>, k: usize, sem: &Semantics) -> UnrollingReturn<'ctx> {
    let bound = paths[0].len() - 1;
    match formula {
        AstNode::UnOp {operator, operand} => {
            match operator {
                UnaryOperator::Negation => {
                    UnrollingReturn::Bool(unroll_ltl_formula(ctx, operand, paths, mapping, k, sem).unwrap_bool().not())
                }
                UnaryOperator::Globally => {
                    let mut constraints = Vec::new();
                    for i in k..=bound {
                        constraints.push(unroll_ltl_formula(ctx, operand, paths, mapping, i, sem).unwrap_bool());
                    }
                    let refs: Vec<&Bool> = constraints.iter().collect();
                    UnrollingReturn::Bool(Bool::and(ctx, &refs))
                }
                UnaryOperator::Eventually => {
                    let mut constraints = Vec::new();
                    for i in k..=bound {
                        constraints.push(unroll_ltl_formula(ctx, operand, paths, mapping, i, sem).unwrap_bool());
                    }
                    let refs: Vec<&Bool> = constraints.iter().collect();
                    UnrollingReturn::Bool(Bool::or(ctx, &refs))
                }
                UnaryOperator::Next => {
                    if k != bound {
                        // We are not on the final state, so we can continue
                        unroll_ltl_formula(ctx, operand, paths, mapping, k + 1, sem)
                    }else {
                        match sem {
                            Semantics::Pes => UnrollingReturn::Bool(Bool::from_bool(ctx, false)),
                            Semantics::Opt => UnrollingReturn::Bool(Bool::from_bool(ctx, true)),
                            Semantics::Hpes => {
                                let halted = is_halted(ctx, paths);
                                let eval_result = unroll_ltl_formula(ctx, operand, paths, mapping, k, sem).unwrap_bool();
                                UnrollingReturn::Bool(Bool::and(ctx, &[&halted, &eval_result]))
                            }
                            Semantics::HOpt => {
                                let not_halted = is_halted(ctx, paths).not();
                                let eval_result = unroll_ltl_formula(ctx, operand, paths, mapping, k, sem).unwrap_bool();
                                UnrollingReturn::Bool(Bool::or(ctx, &[&not_halted, &eval_result]))
                            }
                        }
                    }
                }
            }
        }
        AstNode::BinOp {operator, lhs, rhs} => {
            match operator {
                BinOperator::Equality => {
                    match (
                        unroll_ltl_formula(ctx, lhs, paths, mapping, k, sem),
                        unroll_ltl_formula(ctx, rhs, paths, mapping, k, sem),
                    ) {
                        (UnrollingReturn::Bool(b1), UnrollingReturn::Bool(b2)) => UnrollingReturn::Bool(b1._eq(&b2)),
                        (UnrollingReturn::Var(v1), UnrollingReturn::Var(v2)) => match (v1.as_int(), v2.as_int()) {
                            (Some(i1), Some(i2)) => UnrollingReturn::Bool(i1._eq(&i2)),
                            _ => match (v1.as_bv(), v2.as_bv()) {
                                (Some(bv1), Some(bv2)) => UnrollingReturn::Bool(bv1._eq(&bv2)),
                                _ => panic!("Invalid comparison"),
                            }
                        },
                        _ => panic!("Invalid comparison")
                    }
                }
                BinOperator::Conjunction => {
                    let lhs_bool = unroll_ltl_formula(ctx, lhs, paths, mapping, k, sem).unwrap_bool();
                    let rhs_bool = unroll_ltl_formula(ctx, rhs, paths, mapping, k, sem).unwrap_bool();
                    UnrollingReturn::Bool(Bool::and(ctx, &[&lhs_bool, &rhs_bool]))
                }
                BinOperator::Disjunction => {
                    let lhs_bool = unroll_ltl_formula(ctx, lhs, paths, mapping, k, sem).unwrap_bool();
                    let rhs_bool = unroll_ltl_formula(ctx, rhs, paths, mapping, k, sem).unwrap_bool();
                    UnrollingReturn::Bool(Bool::or(ctx, &[&lhs_bool, &rhs_bool]))
                }
                BinOperator::Implication => {
                    let lhs_bool = unroll_ltl_formula(ctx, lhs, paths, mapping, k, sem).unwrap_bool();
                    let rhs_bool = unroll_ltl_formula(ctx, rhs, paths, mapping, k, sem).unwrap_bool();
                    UnrollingReturn::Bool(lhs_bool.implies(&rhs_bool))
                }
            }
        }
        AstNode::HIndexedProp {proposition, path_identifier} => {
            // If proposition is not defined, panic!
            // Always exists
            let idx: &usize = mapping.get(path_identifier as &str).unwrap();
            let curr_state = &paths[*idx][k];
            match curr_state.get(proposition as &str) {
                Some(v) => {
                    if let Some(node) = v.as_bool() {
                        return UnrollingReturn::Bool(node)
                    }else {
                        return UnrollingReturn::Var(v.clone())
                    }
                }
                None => panic!("Udnefined variable {}", proposition)
            }
        }
        _ => unreachable!()
    }
}