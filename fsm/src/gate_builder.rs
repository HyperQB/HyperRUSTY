use std::collections::VecDeque;
use expressions::{Expression, Literal as Lit};
use std::fmt::Write as FmtWrite;
use logging::Logger;
use crate::parser::split_on_value;
use crate::symbol_map::SymbolMap;


// ---------- QCIR builder ----------
// New version: Sep. 2025

// #[derive(Debug)]
// pub enum LowerError { Temporal(&'static str) }


/// This function will take the CDF and create the gates
/// We will print out the gates and the connections between the gates
/// This will be removed and combined into the expression_to_fsm function at some point
///
/// The function takes an expression like And(Or(Literal(Atom("a")),Literal(Atom("b"))),Literal(Atom("c")))
/// We can see we have an and gate and an or gate
/// We want to set gate 1 to be Or(a,b) and gate 2 to be And(gate1,c)
///
/// # Arguments
/// * `expression` - The expression to create the gates from
/// * `logger` - The logger
/// * `starting_gate` - The starting gate number
/// * `layers` - The number of layers
/// * `symbol_map` - The symbol map
pub fn create_gates_from_cdf(
    expression: &Expression,
    logger: &Logger,
    starting_gate: i32,
    layers: i32,
    symbol_map: &mut SymbolMap
) -> (String, i32, Vec<i32>) {

    let mut max_gate_number = starting_gate; // The current gate number
    let max_gate_number = &mut max_gate_number; // ?
    let mut output_string = String::new();
    let mut stack: VecDeque<(&Expression, usize, bool)> = VecDeque::new(); // (expression, previous_layers_string_index)
    let mut next_stack: VecDeque<(&Expression, usize, bool)> = VecDeque::new(); // (expression, previous_layers_string_index)
    let mut conjunction_gates: Vec<i32> = Vec::new(); // the ands for the layers

    write!(output_string, "### Start building model\n");
    // We have to keep track of the current layer and the current model
    for layer in 0..layers {
        conjunction_gates.push(*max_gate_number+1);
        let mut initial_stack = true;
        let mut current_layer_string: Vec<String> = vec![];
        let mut previous_layer_string: Vec<String> = vec!["".to_owned()];
        stack.push_back((expression, 0, false));

        // let mut stack_thislayer: VecDeque<String> = VecDeque::new();
        let mut this_layer: VecDeque<String> = VecDeque::new();
        // let mut temp_currstep: Vec<String> = Vec::new();


        while let Some(curr_expres) = stack.pop_back(){
            let curr_expression     = curr_expres.0;
            let parent_string_index = curr_expres.1;
            let negation            = curr_expres.2;

            // println!("{:?}", curr_expression);
            // println!("{:?}", parent_string_index);
            // println!("{:?}", negation);
            

            match curr_expression {
                Expression::MAnd(inner) | Expression::MOr(inner) => {
                    *max_gate_number += 1;
                    match curr_expression {
                        Expression::MAnd(_) => {
                            let mut current_output = String::new();
                            if logger.get_mode(){
                                write!(current_output, "g{} = and(", *max_gate_number).expect("Should have been able to write to string");
                            } else {
                                write!(current_output, "{} = and(", *max_gate_number).expect("Should have been able to write to string");
                            }
                            if negation{
                                write!(previous_layer_string[parent_string_index as usize], "-{},", *max_gate_number).expect("Should have been able to write to string");
                            } else{
                                write!(previous_layer_string[parent_string_index as usize], "{},", *max_gate_number).expect("Should have been able to write to string");
                            }
                            current_layer_string.push(current_output);
                            // append to next stack the inner vector. each expression should be incremented so 1,2,3,4
                            for expression in inner {
                                next_stack.push_back((expression, current_layer_string.len() - 1, false)); // add the index of the current layer string
                            }

                        }
                        Expression::MOr(_) => {
                            let mut current_output = String::new();
                            if logger.get_mode(){
                                write!(current_output, "g{} = or(", *max_gate_number).expect("Should have been able to write to string");
                            } else {
                                write!(current_output, "{} = or(", *max_gate_number).expect("Should have been able to write to string");
                            }
                            if logger.get_mode(){
                                if negation{
                                    write!(previous_layer_string[parent_string_index as usize], "-g{},", *max_gate_number).expect("Should have been able to write to string");
                                } else{
                                    write!(previous_layer_string[parent_string_index as usize], "g{},", *max_gate_number).expect("Should have been able to write to string");
                                }
                            }else {
                                if negation{
                                    write!(previous_layer_string[parent_string_index as usize], "-{},", *max_gate_number).expect("Should have been able to write to string");
                                } else{
                                    write!(previous_layer_string[parent_string_index as usize], "{},", *max_gate_number).expect("Should have been able to write to string");
                                }
                            }
                            current_layer_string.push(current_output);
                            // append to next stack the inner vector. each expression should be incremented so 1,2,3,4
                            for expression in inner {
                                next_stack.push_back((expression, current_layer_string.len() - 1, false)); // add the index of the current layer string
                            }
                        }
                        _ => {}
                    }
                }
                Expression::And(left, right) | Expression::Or(left, right) => {
                    let mut current_output = String::new();
                    *max_gate_number += 1;
                    if logger.get_mode(){
                        current_output.push_str("g");
                    }
                    match curr_expression {
                        Expression::And(_,_) => {
                            write!(current_output, "{} = and(", 
                                *max_gate_number).expect("Should have been able to write to string");
                        }
                        Expression::Or(_,_) => {
                            write!(current_output, "{} = or(", 
                                *max_gate_number).expect("Should have been able to write to string");
                        }
                        _ => {}
                    }
                    current_layer_string.push(current_output);    
                    next_stack.push_back((right, current_layer_string.len() - 1, false));
                    next_stack.push_back((left,  current_layer_string.len() - 1, false));


                    if negation         { write!(previous_layer_string[parent_string_index as usize], "-"); } // quick patch
                    if logger.get_mode(){ write!(previous_layer_string[parent_string_index as usize], "g"); } // quick patch
                    write!(previous_layer_string[parent_string_index as usize], "{},", *max_gate_number).unwrap();

                }
                Expression::Literal(lit) => {
                    match lit {
                        Lit::Atom(atom) => {
                            let mut next_layer = layer;
                            if atom.contains("'") {
                                next_layer += 1;
                            }
                            let atom = atom.trim_end_matches("'");
                            let atom = atom.to_string() + "_" + &*next_layer.to_string();

                            if negation { write!(previous_layer_string[parent_string_index as usize], "-"); } // quick patch
                            if let Some(&gate_number) = symbol_map.get(&atom) {
                                if logger.get_mode(){
                                    let output_gate = crate::helper_functions::replace_last_occurrence(&atom, "_", "[").to_string() + "]";
                                    write!(previous_layer_string[parent_string_index as usize], 
                                        "{},", output_gate).expect("Should have been able to write to string");

                                } else{
                                    write!(previous_layer_string[parent_string_index as usize], 
                                        "{},", gate_number).expect("Should have been able to write to string");

                                }
                            } else {
                                let optimize_atom = atom.clone();
                                let optimize_atom = split_on_value(&optimize_atom, '_').0;

                                symbol_map.insert(optimize_atom.clone(), max_gate_number);
                                let current_gate = symbol_map.get(&atom).unwrap();
                                if logger.get_mode() {
                                    let output_gate = crate::helper_functions::replace_last_occurrence(&atom, "_", "[").to_string() + "]";
                                    write!(previous_layer_string[parent_string_index as usize],
                                        "{},", output_gate).expect("Should have been able to write to string");
                                } else{
                                    write!(previous_layer_string[parent_string_index as usize], 
                                        "{},", current_gate).expect("Should have been able to write to string");
                                }
                            }
                        }
                        _ => unreachable!("We are not using NegLiteral right now, should not have gotten here")
                    }
                }
                Expression::Neg(inner) => {
                    stack.push_back((inner, parent_string_index, !negation));
                }
                Expression::True => {
                    // stack.push_back(curr_expression);
                }
                Expression::False => {
                    // stack.push_back(!curr_expression);
                }
                _ => {
                    // println!("{:?}", curr_expression);
                    // println!("Not implemented yet?");
                }
            }

            // if current stack is empty then we need to switch the stacks with mem swap
            if stack.is_empty() {
                std::mem::swap(&mut stack, &mut next_stack);
                // append previous layer string to output string
                if !initial_stack {
                    for string in previous_layer_string.iter(){
                        // take off trailing comma and add ) but only if there is a comma
                        if string.ends_with(","){
                            let string = string.trim_end_matches(",");
                            let string = string.to_string() + ")\n";

                            // THH: small patch to avoid forward gate-referencing
                            ////////////////////////////////////////////////////////////
                            // write!(output_string, "{}", string).expect("Should have been able to write to string");   
                            ////////////////////////////////////////////////////////////
                            this_layer.push_back(string);
                        }
                    }
                } else{
                    initial_stack = false;
                }

                // set previous layer string to current layer string
                previous_layer_string = current_layer_string.clone();
                // clear current layer string
                current_layer_string.clear();
            }

        }

        // THH: small patch to avoid forward gate-referencing
        ////////////////////////////////////////////////////////////
        for string in this_layer.iter().rev(){
            write!(output_string, "{}", string).expect("Should have been able to write to string");
            // take off trailing comma and add ) but only if there is a comma
            if string.ends_with(","){
                let string = string.trim_end_matches(",");
                let string = string.to_string() + ")\n";
                write!(output_string, "{}", string).expect("Should have been able to write to string");
            }
        }
        ////////////////////////////////////////////////////////////
        
    }

    if conjunction_gates.len() == 1 {
        return (output_string, *max_gate_number, conjunction_gates);
    }
    // Final conjunct of transitions of 0..layers
    if logger.get_mode() {
        write!(output_string, "g{} = and({})\n", *max_gate_number+1, conjunction_gates.iter().map(|gate| format!("g{}", gate)).collect::<Vec<String>>().join(",")).expect("Should have been able to write to string");
    } else{
        write!(output_string, "{} = and({})\n", *max_gate_number+1, conjunction_gates.iter().map(|gate| gate.to_string()).collect::<Vec<String>>().join(",")).expect("Should have been able to write to string");
    }
    return (output_string, *max_gate_number+1, vec![0]);
}



















////////////////////////
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_gates_simple(){
        let expression = r"a/\a'";
        let logger = Logger::new(true, 1);
        let fsm = crate::input_to_expressions::input_to_expression(expression);
        // println!("{:?}", fsm);
        let (output, _, _) = create_gates_from_cdf(&fsm, &logger, 0, 1, &mut SymbolMap::new(1,1));
        // println!("{}", output);
        assert_eq!(output, "g1 = and(a[1],a[0])\n");
    }

    #[test]
    fn test_gates_complex(){
        let logger = Logger::new(false, 2);
        let expression = r"((a)->(a'\/b'))";
        let fsm = crate::input_to_expressions::input_to_expression(expression);
        // println!("{:?}", fsm);
        let (output, _, _) = create_gates_from_cdf(&fsm, &logger, 0, 1, &mut SymbolMap::new(1,1));
        // println!("{}", output);
        assert_eq!(output, "1 = or(-2,5,3)\n");
    }

    #[test]
    fn test_gates_complex2(){
        let logger = Logger::new(true, 1);
        let expression = r"((a)->(a'\/~a'))/\((~a)->(~a'))";
        let fsm = crate::input_to_expressions::input_to_expression(expression);
        // println!("{:?}", fsm);
        create_gates_from_cdf(&fsm, &logger, 0, 1, &mut SymbolMap::new(1,1));
    }

    #[test]
    fn test_m_gates(){
        let logger = Logger::new(true, 1);
        let expression = r"(a/\b/\c)";
        let fsm = crate::input_to_expressions::input_to_expression(expression);
        // println!("{:?}", fsm);
        let (output, _, _) = create_gates_from_cdf(&fsm, &logger, 0, 2, &mut SymbolMap::new(1,2));
        // println!("{}", output);
        assert_eq!(output, "g1 = and(c[0],b[0],a[0])\ng11 = and(c[1],b[1],a[1])\ng12 = and(g1,g11)\n")
    }

    #[test]
    fn test_non_recursive(){
        let logger = Logger::new(true, 1);
        let expression = r"(~a/\b)\/(a'/\b'/\c')";
        let fsm = crate::input_to_expressions::input_to_expression(expression);
        // println!("{:?}", fsm);
        let (output, _, _) = create_gates_from_cdf(&fsm, &logger, 0, 2, &mut SymbolMap::new(1,2));
        // println!("{}", output);
    }

}