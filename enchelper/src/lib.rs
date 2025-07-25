use std::collections::HashMap;
use parser::{
    UnaryOperator, BinOperator,
    AstNode,
};

#[derive(Debug, Clone)]
pub enum Semantics {
    Pes,
    Opt,
    Hpes,
    Hopt,
}

// Creates a mapping of the quantified path variables to their corresponding
// index in the state set.
pub fn create_path_mapping(formula: &AstNode, k: usize) -> HashMap<&str, usize> {
    let mut mapping = HashMap::<&str, usize>::new();
    match formula {
        AstNode::HAQuantifier{identifier, form} |
        AstNode::HEQuantifier{identifier, form} => {
            // Recursively map inner quantifiers.
            mapping.extend(create_path_mapping(form, k + 1));
            // Update mapping
            mapping.insert(identifier, k);
            // Return the result
            mapping
        }
        _ => mapping
    }
}

    pub fn inner_ltl(formula: &AstNode) -> &AstNode {
        match formula {
            AstNode::HAQuantifier{identifier: _, form} |
            AstNode::HEQuantifier{identifier: _, form} |
            AstNode::AAQuantifier{identifier: _, form} |
            AstNode::AEQuantifier{identifier: _, form} => {
                inner_ltl(form)
            }
            _ => formula
        }
    }

pub fn is_hltl(formula: &AstNode) -> bool {
    match formula {
        AstNode::HAQuantifier{identifier: _, form} |
        AstNode::HEQuantifier{identifier: _, form} => is_hltl(form),
        AstNode::AAQuantifier{identifier: _, form: _} |
        AstNode::AEQuantifier{identifier: _, form: _} => false,
        _ => true
    }
}

pub fn is_ahltl(formula: &AstNode) -> bool {
    !is_hltl(formula)
}

pub fn get_path_identifiers(formula: &AstNode) -> Vec<&str> {
    match formula {
        AstNode::HAQuantifier{identifier, form} |
        AstNode::HEQuantifier{identifier, form} => {
            // Recursively find inner paths.
            let mut path_list = get_path_identifiers(form);
            // The result is reversed, so we reverse it again
            path_list.reverse();
            // Update the list with the current identifier
            path_list.push(identifier);
            // Reverse the result
            path_list.reverse();
            // Return the result
            path_list
            
        }
        _ => Vec::<&str>::new()
    }
}

pub fn get_traj_identifiers(formula: &AstNode) -> Vec<&str> {
    match formula {
        AstNode::AAQuantifier{identifier, form} |
        AstNode::AEQuantifier{identifier, form} => {
            // Recursively find inner paths.
            let mut traj_list = get_traj_identifiers(form);
            // The result is reversed, so we reverse it again
            traj_list.reverse();
            // Update the list with the current identifier
            traj_list.push(identifier);
            // Reverse the result
            traj_list.reverse();
            // Return the result
            traj_list
        }
        AstNode::HAQuantifier{identifier:_, form} |
        AstNode::HEQuantifier{identifier:_, form} => get_traj_identifiers(form),
        _ => Vec::<&str>::new()
    }
}

// Returns existential trajectories in order
pub fn get_exists_trajs(formula: &AstNode) -> Vec<&str> {
    match formula {
        AstNode::AEQuantifier{identifier, form} => {
            // Recursively find inner paths.
            let mut exists_list = get_exists_trajs(form);
            // The result is reversed, so we reverse it again
            exists_list.reverse();
            // Update the list with the current identifier
            exists_list.push(identifier);
            // Reverse the result
            exists_list.reverse();
            // Return the result
            exists_list
        }
        AstNode::HAQuantifier{identifier:_, form} |
        AstNode::HEQuantifier{identifier:_, form} |
        AstNode::AAQuantifier{identifier:_, form} => get_exists_trajs(form),
        _ => Vec::<&str>::new()
    }
}

// Returns universal trajectories in order
pub fn get_forall_trajs(formula: &AstNode) -> Vec<&str> {
    match formula {
        AstNode::AAQuantifier{identifier, form} => {
            // Recursively find inner paths.
            let mut forall_list = get_forall_trajs(form);
            // The result is reversed, so we reverse it again
            forall_list.reverse();
            // Update the list with the current identifier
            forall_list.push(identifier);
            // Reverse the result
            forall_list.reverse();
            // Return the result
            forall_list
        }
        AstNode::HAQuantifier{identifier:_, form} |
        AstNode::HEQuantifier{identifier:_, form} |
        AstNode::AEQuantifier{identifier:_, form} => get_forall_trajs(form),
        _ => Vec::<&str>::new()
    }
}

// Checks whether the formula has only existential trajectory quantifiers
pub fn is_E(formula: &AstNode) -> bool {
    match formula {
        AstNode::AAQuantifier{identifier:_, form:_} => false,
        AstNode::HAQuantifier{identifier:_, form} |
        AstNode::HEQuantifier{identifier:_, form} |
        AstNode::AEQuantifier{identifier:_, form} => is_E(form),
        _ => true
    }
}

// Checks whether the formula has only universal trajectory quantifiers
pub fn is_A(formula: &AstNode) -> bool {
    match formula {
        AstNode::AEQuantifier{identifier:_, form:_} => false,
        AstNode::HAQuantifier{identifier:_, form} |
        AstNode::HEQuantifier{identifier:_, form} |
        AstNode::AAQuantifier{identifier:_, form} => is_A(form),
        _ => true
    }
}

// Checks whether the formula's trajectory quantifiers are AE
// There needs to be more than 1 quantifiers
pub fn is_AE(formula: &AstNode) -> bool {
    // If the formula consists of only one quantifier, reject
    if is_A(formula) | is_E(formula) {
        return false;
    }
    check_AE_rec(formula)
}

fn check_AE_rec(formula: &AstNode) -> bool {
    match formula {
        AstNode::AEQuantifier{identifier:_, form} => {
            match &**form {
                AstNode::AAQuantifier{identifier:_, form:_} => false,
                _ => check_AE_rec(form),
            }
        },
        AstNode::HAQuantifier{identifier:_, form} |
        AstNode::HEQuantifier{identifier:_, form} |
        AstNode::AAQuantifier{identifier:_, form} => check_AE_rec(form),
        _ => true
    }
}

// Checks whether the formula's trajectory quantifiers are EA
// There needs to be more than 1 quantifiers
pub fn is_EA(formula: &AstNode) -> bool {
    // If the formula consists of only one quantifier, reject
    if is_A(formula) | is_E(formula) {
        return false;
    }
    check_EA_rec(formula)
}

fn check_EA_rec(formula: &AstNode) -> bool {
    match formula {
        AstNode::AAQuantifier{identifier:_, form} => {
            match &**form {
                AstNode::AEQuantifier{identifier:_, form:_} => false,
                _ => check_EA_rec(form),
            }
        },
        AstNode::HAQuantifier{identifier:_, form} |
        AstNode::HEQuantifier{identifier:_, form} |
        AstNode::AEQuantifier{identifier:_, form} => check_EA_rec(form),
        _ => true
    }
}

pub fn detect_quantifier_order(formula: &AstNode) -> u8 {
    let mut seq = Vec::new();
    let mut current = formula;

    loop {
        match current {
            AstNode::HAQuantifier { form, .. } => {
                seq.push('A');
                current = form;
            }
            AstNode::HEQuantifier { form, .. } => {
                seq.push('E');
                current = form;
            }
            // skip over hyper quantifiers
            AstNode::AAQuantifier { form, .. }
            | AstNode::AEQuantifier { form, .. } => {
                current = form;
            }
            // once we hit anything else, stop
            _ => break,
        }
    }
    println!("{:?}", seq);
    // Check for the patterns we're interested in
    match seq.as_slice() {
        ['A', 'E'] => 1,  // AE pattern
        ['E', 'A'] => 2,  // EA pattern
        _ => 0  // Other patterns not supported
    }
}


pub fn starts_with_g_or_f(formula: &AstNode) -> bool {
    let inner_formula = inner_ltl(formula);
    match inner_formula {
        AstNode::UnOp { operator, .. } => {
            matches!(operator, UnaryOperator::Globally | UnaryOperator::Eventually)
        }
        _ => false,
    }
}


pub fn has_no_until_or_release(formula: &AstNode) -> bool {
    match formula {
        AstNode::BinOp { operator, lhs, rhs } => {
            match operator {
                BinOperator::Until | BinOperator::Release => false,
                _ => {
                    has_no_until_or_release(lhs) && has_no_until_or_release(rhs)
                }
            }
        }
        
        AstNode::UnOp { operand, .. } => {
            has_no_until_or_release(operand)
        }
        
        AstNode::HAQuantifier { form, .. } |
        AstNode::HEQuantifier { form, .. } |
        AstNode::AAQuantifier { form, .. } |
        AstNode::AEQuantifier { form, .. } => {
            has_no_until_or_release(form)
        }
        

        AstNode::HIndexedProp { .. } |
        AstNode::AIndexedProp { .. } |
        AstNode::Constant { .. } => true,
    }
}
