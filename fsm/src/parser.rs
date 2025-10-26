use std::any::{Any};
use expressions::{Expression, Literal};
use std::collections::HashMap;
use std::fmt::Write as FmtWrite;
use crate::symbol_map::SymbolMap;
use stacker;
use logging::{Logger, raise_error};


/// Helper function that splits a string on a value
pub(crate) fn split_on_value(value: &str, split_char: char) -> (String, String){
    let res = value.rfind(split_char);
    if res.is_none() {
        raise_error(&*format!("Error: {} does not contain {}. Something is not being input into unrolling correctly. {} should be in the form of 'variable name'_'model name'", value, split_char, value), 5);
        panic!();
    }
    let idk = value.rfind(split_char).unwrap();
    let left = value[..idk].to_string();
    let right = value[idk+1..].to_string();
    (left, right)
}

/// Helper function that gets the difference between a character and 'A'
fn char_difference_from_a(c: char) -> Option<u32> {
    // Convert 'A' to its Unicode scalar value
    let base_char = 'A';
    let base_value = base_char as u32;

    // Convert the input character to its Unicode scalar value
    let char_value = c as u32;

    // Calculate the difference
    if char_value >= base_value {
        Some(char_value - base_value)
    } else {
        None // Return None if the character is before 'A' in Unicode order
    }
}

fn char_difference_to_a(i: u32) -> char {
    // Convert 'A' to its Unicode scalar value
    let base_char = 'A';
    let base_value = base_char as u32;

    // Calculate the character value
    let char_value = base_value + i;

    // Convert the Unicode scalar value to a character
    char::from_u32(char_value).unwrap()
}

/// This is the parser that will be getting used in the gate functions
pub struct Parser<'a> {
    expression: Box<Expression>,
    model_map: &'a SymbolMap,
    debug: bool,
    layers: i32,
    max_gate_number: i32,
    original_gate: i32,
    semantics: String,
    logger: Logger,
}

impl Parser<'_>{
    pub fn new(expression: Box<Expression>, model_map: &SymbolMap, debug: bool, layers: i32, max_gate_number: i32, semantics: String, logger: Logger) -> Parser {
        Parser {
            expression,
            model_map,
            debug,
            layers,
            max_gate_number,
            original_gate: max_gate_number,
            semantics,
            logger
        }
    }

    // fn get_expression(&self) -> Box<Expression> {
    //     self.expression.clone()
    // }

    /// Function takes output from a layer in the create_gates function and then checks edge cases
    ///
    /// Its purpose is to fix a bug where things like G(a_A) would give no output because it would
    /// go into the create_gates function and not reach anything that prints an output (like and)
    /// The literals only return their gate number so this is needed
    ///
    /// Also, if we have something like G(neg(a_A/\a_B)) then we only print the and, not the negation
    /// This also fixes that bug
    fn get_output_gates(&mut self, returned_gate: &str, neg: bool, variables: &mut Vec<Box<dyn Any>>){
        if let Ok(max) = returned_gate.parse::<i32>() {
            // First, lets check if it is a single gate
            // This happens when the max_gate_number is equal to the old max_gate_number
            // We don't want to print yet, we want to store in an array and print at the end in one
            // big 'and' gate which will optimize the output

            if self.max_gate_number >= max {
                if neg {
                    variables.push(Box::new(-max));
                } else {
                    variables.push(Box::new(max));
                }
            } else if neg { // This is the case that there was a neg after the last printing statement
                variables.push(Box::new(-self.max_gate_number));
            } else { // simply push it if no edge case
                variables.push(Box::new(self.max_gate_number));
            }
            // increment max_gate_number if it wasn't a literal
            if max > self.max_gate_number {
                self.max_gate_number = max;
            }
        } else { // this is case if it was just a single variable
            if neg{
                variables.push(Box::new("-".to_owned() +returned_gate));
            } else {
                variables.push(Box::new(returned_gate.to_owned()));

            }
        }
    }


    /// This is a modified create_gates function that will be used for the LTL part of the formula
    /// It takes the extra parameters of the model_map and uses that to create the gates from each
    /// model. It will then return the gates that are used in the LTL part of the formula.
    pub fn create_gates_from_cdf(&mut self, expression: &Expression) -> (String, i32, HashMap<String,i32>, Vec<String>) {
        // Values used in loop
        let mut symbol_map: HashMap<String,i32> = HashMap::new();
        let output_string = &mut String::new();

        fn recursive_gate_print(max_gate_number: &mut i32, expression: &Expression, symbol_map: &mut HashMap<String, i32>, layer: i32, file: &mut String, debug: bool, model_maps: &SymbolMap, logger: &Logger) -> (String, bool) {
            stacker::maybe_grow(32*1024, 1024*1024, || {
            // match the expression, used for the different writing of the gates
            match expression {
                Expression::MOr(inner) | Expression::MAnd(inner) => {
                    // vector for printing gates and such
                    let mut vec: Vec<(String,bool)> = Vec::new();
                    for expression in inner {
                        let ret_val = recursive_gate_print(max_gate_number, expression, symbol_map, layer, file, debug, model_maps, logger);
                        vec.push(ret_val);
                    }
                    *max_gate_number += 1;

                    // write the output string, it should be in form of g{max_gate_number} = or(g1,g2,g3,.....,gn)
                    match expression {
                        Expression::MOr(_) => {
                            if debug {
                                write!(
                                    file,
                                    "g{} = or({})\n",
                                    max_gate_number,
                                    vec.iter().map(|(gate, neg)| {
                                        let gate_str = if gate.chars().all(|c| c.is_numeric()) {
                                            format!("g{}", gate)
                                        } else {
                                            gate.to_string()
                                        };
                                        if *neg { format!("-{}", gate_str) } else { gate_str }
                                    }).collect::<Vec<String>>().join(","),
                                ).expect("Should have been able to write to string");
                            } else {
                                write!(
                                    file,
                                    "{} = or({})\n",
                                    max_gate_number,
                                    vec.iter().map(|(gate, neg)| if *neg { format!("-{}", gate) } else { gate.to_string() }).collect::<Vec<String>>().join(","),
                                ).expect("Should have been able to write to string");
                            }

                        }
                        Expression::MAnd(_) => {
                            if debug {
                                write!(
                                    file,
                                    "g{} = and({})\n",
                                    max_gate_number,
                                    vec.iter().map(|(gate, neg)| {
                                        let gate_str = if gate.chars().all(|c| c.is_numeric()) {
                                            format!("g{}", gate)
                                        } else {
                                            gate.to_string()
                                        };
                                        if *neg { format!("-{}", gate_str) } else { gate_str }
                                    }).collect::<Vec<String>>().join(","),
                                ).expect("Should have been able to write to string");
                            } else {
                                write!(
                                    file,
                                    "{} = and({})\n",
                                    max_gate_number,
                                    vec.iter().map(|(gate, neg)| if *neg { format!("-{}", gate) } else { gate.to_string() }).collect::<Vec<String>>().join(","),
                                ).expect("Should have been able to write to string");
                            }
                        }
                        _ => {}
                    }
                    return ((*max_gate_number).to_string(), false)
                }
                Expression::And(left, right) => {
                    let (left_gate, left_neg) = recursive_gate_print(max_gate_number, left, symbol_map, layer, file, debug, model_maps,logger);
                    let (right_gate, right_neg) = recursive_gate_print(max_gate_number, right, symbol_map, layer, file, debug, model_maps,logger);
                    *max_gate_number += 1;
                    // write to output string
                    if debug{ //****************** debug print *****************
                        write!(
                            file,
                            "g{} = and({},{})\n",
                            max_gate_number,
                            if left_neg { format!("-g{}", left_gate) } else {
                                if left_gate.starts_with(|c: char| c.is_digit(10)) {
                                    format!("g{}", left_gate)
                                } else {
                                    left_gate.to_string()
                                }
                            },
                            if right_neg { format!("-g{}", right_gate) } else {
                                if right_gate.starts_with(|c: char| c.is_digit(10)) {
                                    format!("g{}", right_gate)
                                } else {
                                    right_gate.to_string()
                                }
                            }
                        ).expect("Should have been able to write to string");
                    } else { // ***************** end debug print *****************
                        write!(file, "{} = and({},{})\n", max_gate_number, if left_neg { format!("-{}", left_gate) } else { left_gate.to_string() }, if right_neg { format!("-{}", right_gate) } else { right_gate.to_string() }).expect("Should have been able to write to string");
                    }
                    return ((*max_gate_number).to_string(), false)
                }

                Expression::Or(left, right) => {
                    let (left_gate, left_neg) = recursive_gate_print(max_gate_number, left, symbol_map, layer, file, debug, model_maps,logger);
                    let (right_gate, right_neg) = recursive_gate_print(max_gate_number, right, symbol_map, layer, file, debug, model_maps,logger);
                    *max_gate_number += 1;
                    if debug{ //****************** debug print *****************
                        write!(
                            file,
                            "g{} = or({},{})\n",
                            max_gate_number,
                            if left_neg { format!("-{}", left_gate) } else {
                                if left_gate.starts_with(|c: char| c.is_numeric()) {
                                    format!("g{}", left_gate)
                                } else {
                                    left_gate.to_string()
                                }
                            },
                            if right_neg { format!("-{}", right_gate) } else {
                                if right_gate.starts_with(|c: char| c.is_numeric()) {
                                    format!("g{}", right_gate)
                                } else {
                                    right_gate.to_string()
                                }
                            }
                        ).expect("Should have been able to write to string");
                    } else{// ***************** end debug print *****************
                        write!(file, "{} = or({},{})\n", max_gate_number, if left_neg { format!("-{}", left_gate) } else { left_gate.to_string() }, if right_neg { format!("-{}", right_gate) } else { right_gate.to_string() }).expect("Should have been able to write to string");
                    }
                    return ((*max_gate_number).to_string(), false)
                }
                // ************ This literal part is what is different between the two functions ************
                Expression::Literal(lit) => {
                    match lit {
                        Literal::Atom(atom) => {
                            let mut next_layer = layer;
                            // Deal if is going to the next state
                            if atom.contains("'") {
                                next_layer += 1;
                            }

                            // Get which model this var is a part of
                            let (variable,model) = split_on_value(atom, '_');
                            let model = char_difference_from_a(model.chars().next().unwrap()).unwrap() as i32;
                            let atom = variable.to_string() + "_" + &*next_layer.to_string();

                            if let Some(&gate_number) = model_maps.get_symbol_map(&model).get(&atom) {
                                if debug{
                                    // replace _ with [ and add ] at the end

                                    return (crate::helper_functions::replace_last_occurrence(&atom, "_", "[").to_string() + "]_" + &*char_difference_to_a(model as u32).to_string(), false);

                                }
                                return (gate_number.to_string(), false)
                            } else {
                                let (var,_) = split_on_value(&atom, '_');
                                logger.log(&*format!("Literal {} not found in model {}\nPlease make sure that the literal is as named in the hq file",var, model+1), 5);
                                panic!("Literal not found in model");
                            }
                        }
                        Literal::NegAtom(_) => {unreachable!("Never created NegAtoms")}
                    }
                }
                // *********************** End Changes ***********************

                Expression::Neg(inner) => {
                    let (gate, neg) = recursive_gate_print(max_gate_number, inner, symbol_map, layer, file, debug, model_maps, logger);
                    // if it is already negated, then we can remove the negation
                    if neg {
                        return (gate, false)
                    } else {
                        return (gate, true)
                    }
                }

                _ => {
                    // println!("Not implemented yet: {:?}", expression);
                    (0.to_string(), false)
                }
            }
        })}

        // Run the recursive function and then output it
        let mut gates = vec![];
        for i in 0..self.layers {
            let neg : bool;
            let max;
            (max, neg) = recursive_gate_print(&mut self.max_gate_number, expression, &mut symbol_map, i, output_string, self.debug, self.model_map, &self.logger);
            // If the layer only goes up by one, then it was just a single gate so it wasn't printed
            // Get the output gates and check edge cases
            self.get_output_gates(&max, neg, &mut gates);
        }

        // format output
        let output_gates: Vec<String> = gates.iter().map(|gate| {
            match gate.downcast_ref::<i32>() {
                Some(gate) => {
                    if self.debug {
                        if *gate < 0 {
                            format!("-g{}", gate.abs())
                        } else {
                            format!("g{}", gate)
                        }
                    } else {
                        gate.to_string()
                    }
                }
                None => {
                    gate.downcast_ref::<String>().unwrap().to_string()
                }
            }
        }).collect();
        return ((*output_string.clone()).parse().unwrap(), self.max_gate_number, symbol_map, output_gates);
    }

    /// This function takes the G expression and processes it. It doesn't need to add any gates, but it does
    /// need to tell what the literals are and if they are negative or not. It should compare this to each models
    /// values at each timestep. So it will take something like G(~a_A\/a_B) and then return
    /// a hashmap of the literals to the gates from its model. a_A is in model A and a_B is in model B.
    fn process_g_expressions(&mut self, expression: &Expression, negated: &mut bool) -> (String, i32, bool) {
        self.logger.log(&*format!("Processing expression: {:?}", expression), 2);
        match expression {
            // single LTL
            Expression::G(inner_expr) | Expression::F(inner_expr) => {
                let (mut output, max_gate, _, gates) = self.create_gates_from_cdf(inner_expr);

                match expression{
                    Expression::G(_) => {
                        if self.debug {
                            write!(output, "g{} = and({})\n", max_gate+1, gates.join(",")).expect("Should have been able to write to string");
                        } else {
                            write!(output, "{} = and({})\n", max_gate+1, gates.join(",")).expect("Should have been able to write to string");
                        }
                    }
                    Expression::F(_) => {
                        if self.debug {
                            write!(output, "g{} = or({})\n", max_gate+1, gates.join(",")).expect("Should have been able to write to string");
                        } else {
                            write!(output, "{} = or({})\n", max_gate+1, gates.join(",")).expect("Should have been able to write to string");
                        }
                    }
                    _ => {
                        self.logger.log(&*format!("You included an expression that we don't support: {:?}", expression),5);
                        panic!(); }
                }

                return (output, max_gate+1, false);
            }

            // Double LTL
            Expression::U(left,right) => { // right and (left or (left_2 U_layer right_2))
                let (mut output, left_max, _, left_gates) = self.create_gates_from_cdf(left);
                self.max_gate_number = left_max;
                self.original_gate= self.max_gate_number;
                let (right_output, right_max, _, right_gates) = self.create_gates_from_cdf(right);
                self.max_gate_number = right_max;
                output.push_str(&right_output);

                let mut z;
                if self.layers-2 >0 {
                    z = (right_max + (self.layers-2)*2+2) as usize;
                } else {
                    z = (right_max+2) as usize;
                }
                if self.semantics == "OPT"{
                    z += 1;
                }
                self.max_gate_number = z as i32;


                for i in 0..self.layers-2{
                    let i = i as usize;
                    if self.debug {
                        write!(output, "g{} = or({}, g{})\n", z, right_gates[i], z-1).expect("Should have been able to write to string");
                        write!(output, "g{} = and({}, g{})\n", z-1, left_gates[i], z-2).expect("Should have been able to write to string");
                        z-=2;
                    } else{
                        write!(output, "{} = or({},{})\n", z, right_gates[i], z-1).expect("Should have been able to write to string");
                        write!(output, "{} = and({},{})\n", z-1, left_gates[i], z-2).expect("Should have been able to write to string");
                        z-=2;
                    }
                }
                // write the final gates

                let layer = (self.layers-2) as usize;
                if self.semantics == "PES" { // last chance, either phi 2 now or next step.
                    if self.debug {
                        write!(output, "g{} = or({}, g{})\n", z, right_gates[layer], z-1).expect("Should have been able to write to string");
                        write!(output, "g{} = and({}, {})\n", z-1, left_gates[layer], right_gates[layer+1]).expect("Should have been able to write to string");
                    } else{
                        write!(output, "{} = or({},{})\n", z, right_gates[layer], z-1).expect("Should have been able to write to string");
                        write!(output, "{} = and({},{})\n", z-1, left_gates[layer], right_gates[layer+1]).expect("Should have been able to write to string");
                    }
                } else if self.semantics == "OPT" { // Not the last chance, as long as phi 1 never fails we are good
                    if self.debug {
                        write!(output, "g{} = or({}, g{})\n", z, right_gates[layer], z-1).expect("Should have been able to write to string");
                        write!(output, "g{} = and({}, g{})\n", z-1, left_gates[layer], z-2).expect("Should have been able to write to string");
                        write!(output, "g{} = or({}, {})\n", z-2, left_gates[layer+1], right_gates[layer+1]).expect("Should have been able to write to string");
                    } else{
                        write!(output, "{} = or({},{})\n", z, right_gates[layer], z-1).expect("Should have been able to write to string");
                        write!(output, "{} = and({},{})\n", z-1, left_gates[layer], right_gates[layer+1]).expect("Should have been able to write to string");
                        write!(output, "{} = or({},{})\n", z-2, left_gates[layer+1], right_gates[layer+1]).expect("Should have been able to write to string");
                    }

                }


                // if we have at least 2 layers, write starting gate as well

                return (output, self.max_gate_number, false);
            }

            // Double LTL
            Expression::R(left,right) => { // right OR (left AND (left_2 U_layer right_2))
                let (mut output, left_max, _, left_gates) = self.create_gates_from_cdf(left);
                self.max_gate_number = left_max;
                self.original_gate= self.max_gate_number;
                let (right_output, right_max, _, right_gates) = self.create_gates_from_cdf(right);
                self.max_gate_number = right_max;
                output.push_str(&right_output);
                let mut z;
                if self.layers-2 >0 {
                    z = (right_max + (self.layers-2)*2+2) as usize;
                } else {
                    z = (right_max+2) as usize;
                }
                if self.semantics == "PES"{
                    z += 1;
                }
                self.max_gate_number = z as i32;

                for i in 0..self.layers-2{
                    let i = i as usize;
                    if self.debug {
                        write!(output, "g{} = and({}, g{})\n", z, right_gates[i], z-1).expect("Should have been able to write to string");
                        write!(output, "g{} = or({}, g{})\n", z-1, left_gates[i], z-2).expect("Should have been able to write to string");
                        z-=2;
                    } else{
                        write!(output, "{} = and({},{})\n", z, right_gates[i], z-1).expect("Should have been able to write to string");
                        write!(output, "{} = or({},{})\n", z-1, left_gates[i], z-2).expect("Should have been able to write to string");
                        z-=2;
                    }
                }
                // write the final gates
                let layer = (self.layers-2) as usize;
                if self.semantics == "OPT"{
                    if self.debug {
                        write!(output, "g{} = and({}, g{})\n", z, right_gates[layer], z-1).expect("Should have been able to write to string");
                        write!(output, "g{} = or({}, {})\n", z-1, left_gates[layer], right_gates[layer+1]).expect("Should have been able to write to string");
                    } else{
                        write!(output, "{} = and({},{})\n", z, right_gates[layer], z-1).expect("Should have been able to write to string");
                        write!(output, "{} = or({},{})\n", z-1, left_gates[layer], right_gates[layer+1]).expect("Should have been able to write to string");
                    }
                } else{
                    if self.debug {
                        write!(output, "g{} = and({}, g{})\n", z, right_gates[layer], z-1).expect("Should have been able to write to string");
                        write!(output, "g{} = or({}, g{})\n", z-1, left_gates[layer], z-2).expect("Should have been able to write to string");
                        write!(output, "g{} = and({}, {})\n", z-2, left_gates[layer+1], right_gates[layer+1]).expect("Should have been able to write to string");
                    } else{
                        write!(output, "{} = and({},{})\n", z, right_gates[layer], z-1).expect("Should have been able to write to string");
                        write!(output, "{} = or({},{})\n", z-1, left_gates[layer], z-2).expect("Should have been able to write to string");
                        write!(output, "{} = and({},{})\n", z-2, left_gates[layer+1], right_gates[layer+1]).expect("Should have been able to write to string");
                    }
                }


                // if we have at least 2 layers, write starting gate as well

                return (output, self.max_gate_number, false);
            }

            // Normal gates
            Expression::And(left, right) | Expression::Or(left,right) => {
                let (left_gates, left_max, left_negation) = self.process_g_expressions(left, negated);
                self.max_gate_number = left_max;
                self.original_gate= self.max_gate_number;
                let (right_gates, right_gate_num, right_negation) = self.process_g_expressions(right, negated);
                let mut output = format!("{}{}", left_gates, right_gates);
                // Now and the left and right gates together
                self.max_gate_number = right_gate_num+1;
                match expression{
                    Expression::And(_, _) => {
                        if self.debug {
                            write!(output, "g{} = and({}g{},{}g{})\n", self.max_gate_number, if left_negation { "-" } else { "" }, left_max, if right_negation { "-" } else { "" }, right_gate_num).expect("Should have been able to write to string");
                        } else {
                            write!(output, "{} = and({}{},{}{})\n", self.max_gate_number, if left_negation { "-" } else { "" }, left_max, if right_negation { "-" } else { "" }, right_gate_num).expect("Should have been able to write to string");
                        }
                    }
                    Expression::Or(_, _) => {
                        if self.debug {
                            write!(output, "g{} = or({}g{},{}g{})\n", self.max_gate_number, if left_negation { "-" } else { "" }, left_max, if right_negation { "-" } else { "" }, right_gate_num).expect("Should have been able to write to string");
                        } else {
                            write!(output, "{} = or({}{},{}{})\n", self.max_gate_number, if left_negation { "-" } else { "" }, left_max, if right_negation { "-" } else { "" }, right_gate_num).expect("Should have been able to write to string");
                        }
                    }
                    _ => {unreachable!("Only match on the expressions we defined, so can't reach here")}
                }
                return (output, right_gate_num+1, false);
            }

            // Expression::Neg(inner_expr) => {
            //     let (output,right_gate_num,mut neg) = self.process_g_expressions(inner_expr, &mut !(*negated));
            //     // Negate the gate
            //     neg = !neg;

            //     return (output, right_gate_num, neg);
            // }
            _ => {
                // let test = expression_to_string(expression);
                // println!("Test: {:?}", test);
                unreachable!("Shouldn't have gotten here")}
        }
    }

    /// This is the function called when you want to parse the LTL part of the formula
    pub fn ltl_parser(&mut self) -> (String, i32, bool) {
        // Now run to get the gates it will use
        let expression = &*self.expression.clone();
        // let test = expression_to_string(expression);
        // println!("Test: {:?}", test);
        return self.process_g_expressions(expression, &mut false);
    }
}
