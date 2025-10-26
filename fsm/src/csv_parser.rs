use expressions::*;
use csv::ReaderBuilder;
use std::io::BufRead;
use std::collections::HashMap;
use std::collections::HashSet;
use std::error::Error;
use std::fs::File;
use std::io::{self};
use regex::Regex;
use std::path::Path;

#[derive(Debug, Clone)]
struct VariableStates {
    initial: HashSet<Box<Expression>>,
    next: HashSet<Box<Expression>>,
}

impl VariableStates {
    fn new() -> Self {
        VariableStates {
            initial: HashSet::new(), // TODO: change these to Box<Expression> 
            next: HashSet::new(),
        }
    }

    fn add_initial_state(&mut self, state: Box<Expression>) {
        
        // if !self.initial.is_empty(){
        //     // Modify the existing initial state by removing all current states and inserting the new one
        //     let curr_expr = self.initial.iter().next().unwrap().clone();
        //     if state != curr_expr {
        //         let new_expr: Box<Expression> = Box::new(Expression::Or(curr_expr,state));
        //         self.initial.clear();
        //         self.initial.insert(new_expr);
        //     }

        // } else {
        //     self.initial.insert(state);
        // }
        self.initial.insert(state);
    }

    fn add_next_state(&mut self, state: Box<Expression>) {
        // if !self.next.is_empty(){
        //     // Modify the existing initial state by removing all current states and inserting the new one
        //     let curr_expr = self.next.iter().next().unwrap().clone();
        //     if state != curr_expr {
        //         let new_expr: Box<Expression> = Box::new(Expression::Or(curr_expr,state));
        //         self.next.clear();
        //         self.next.insert(new_expr);
        //     }

        // } else {
        //     self.next.insert(state);
        // }

        self.next.insert(state);
    }

    fn get_initial_states(&self) -> impl Iterator<Item = &Box<Expression>> {
        self.initial.iter()
    }

    fn get_next_states(&self) -> impl Iterator<Item = &Box<Expression>> {
        self.next.iter()
        // Box::new(self.next.iter().cloned().collect())
    }

    // fn initial_states_size(&self) -> usize {
    //     self.initial.len()
    // }

    // fn final_states_size(&self) -> usize {
    //     self.next.len()
    // }
}

#[derive(Debug, Clone)]
struct StateMap {
    variables: HashMap<String, VariableStates>,
}

impl StateMap {
    fn new() -> Self {
        StateMap {
            variables: HashMap::new(),
        }
    }

    // fn add_variable(&mut self, name: String) {
    //     self.variables.insert(name, VariableStates::new());
    // }

    fn add_initial_state(&mut self, name: String, state: Box<Expression>) {
        if let Some(var_states) = self.variables.get_mut(&name) {
            var_states.add_initial_state(state);
        } else {
            let mut var_states = VariableStates::new();
            var_states.add_initial_state(state);
            self.variables.insert(name, var_states);
        }
    }

    fn add_next_state(&mut self, name: String, state: Box<Expression>) {
        if let Some(var_states) = self.variables.get_mut(&name) {
            var_states.add_next_state(state);
        } else {
            let mut var_states = VariableStates::new();
            var_states.add_next_state(state);
            self.variables.insert(name, var_states);
        }
    }

    // fn get_variable_states(&self, name: &str, state_type: &str) -> Option<&HashSet<Box<Expression>>> {
    //     self.variables
    //         .get(name)
    //         .and_then(|var_states| var_states.get_states(state_type))
    // }

    // fn get_initial_states(&self, name: &str) -> Option<impl Iterator<Item = &Box<Expression>>> {
    //     self.variables.get(name).map(|vs| vs.get_initial_states())
    // }

    // fn get_next_states(&self, name: &str) -> Option<impl Iterator<Item = &Box<Expression>>> {
    //     self.variables.get(name).map(|vs| vs.get_next_states())
    // }

    fn collect_all_initial_states(&self) -> HashSet<Box<Expression>> {
        self.variables.values()
            .flat_map(|states| states.get_initial_states().cloned())
            .collect()
    }

    fn collect_all_next_states(&self) -> HashSet<Box<Expression>> {
        self.variables.values()
            .flat_map(|states| states.get_next_states().cloned())
            .collect()
    }

    fn is_empty(&self) -> bool {
        self.variables.is_empty()
    }
}

pub fn csv_to_expr() -> (Box<Expression>, HashMap<String,i32>) {
    // println!(">>> HERE");
    let mut trans_stack: Vec<Box<Expression>> = Vec::new();
    let max_bit_map = parse_vars_file().expect("REASON");
    let copy_max_bit_map = max_bit_map.clone();
    let _ = parse_csv(&mut trans_stack, &max_bit_map);
    return (combine_expr(trans_stack.to_vec()), copy_max_bit_map);
}

// parses vars.txt file to determine max bit order for each variable when blasting bits
fn parse_vars_file() -> io::Result<HashMap<String, i32>> {
    let path = Path::new("nusmv/outputs/vars.txt"); 
    // let path = Path::new("/Volumes/RAMDisk/temp.txt");
    let file = File::open(&path)?;
    let reader = io::BufReader::new(file);
    let mut result_map = HashMap::new();
    // let re = Regex::new(r"(\w+\[\d+\]|\w+) : \{([^}]+)\}").unwrap();
    let re = Regex::new(r"(\S+)\s*: \{([^}]+)\}").unwrap();

    for line in reader.lines() {
        let line = line?;
        if let Some(captures) = re.captures(&line) {
            let variable = captures.get(1).unwrap().as_str().to_string();
            let values_str = captures.get(2).unwrap().as_str();
            let values: Vec<i32> = values_str
                .split(',')
                .map(|s| s.trim().parse().unwrap())
                .collect();
            if let Some(&max_value) = values.iter().max() {
                result_map.insert(variable, max_value);
            }
        }
    }
    for (_, _) in &result_map {
        // println!("+++++RESULT MAP => {} : {}", key, value);
    }

    Ok(result_map)
}

fn parse_csv(trans_stack: &mut Vec<Box<Expression>>, max_bit_map: &HashMap<String, i32>) -> Result<(), Box<dyn Error>> {
    // Open the CSV file for reading
    let file_path = "nusmv/outputs/out.csv";
    // let file_path = "/Volumes/RAMDisk/temp.csv";
    let file = File::open(file_path)?;
    let mut rdr = ReaderBuilder::new()
        .delimiter(b'\t')
        .has_headers(true)
        .from_reader(file);

    // Read the headers
    let headers = rdr.headers()?.clone();
    let curr_id_index = headers.iter().position(|header| header == "CurrID").unwrap();
    let mut prev_id_value = "0".to_string();

    let mut state_vec: Vec<StateMap> = Vec::new();
    // let mut value = state_vec.push(state_map.clone());
    for result in rdr.records() {
        let record = result?;
        let curr_id_value = record.get(curr_id_index).unwrap().to_string();
        let mut state_map = StateMap::new();

        // create new state map for each transition, some transitions in the csv file are on more than one row
        if prev_id_value != curr_id_value {
            if !state_map.is_empty() {
                // println!("STATE MAP: {:#?}", state_map);
                // trans_stack.push(vec_to_expr(&state_vec));
            //     // println!("TRANS STACK: {:?}", trans_stack);
            }
            
        }
        for (i,header) in headers.iter().enumerate() {
            let value = record.get(i).unwrap_or("").to_string();
            if header == "CurrID" || header == "NextID" {
                continue;
            }
            // check if initial or next variable and add to state map accordingly
            if header.starts_with("next(") && header.ends_with(")") {
                let var_name = &header[5..header.len() - 1];
                state_map.add_next_state(var_name.to_string(), state_to_expr(var_name, &value, true, max_bit_map));
            } else {
                state_map.add_initial_state(header.to_string(), state_to_expr(header, &value, false, max_bit_map));
            }    
        }

        // switch to a new state vec for each transition relation
        if curr_id_value == prev_id_value || prev_id_value == "0" {
            // value;
            state_vec.push(state_map.clone())
        } else {
            // if !state_vec.is_empty() {
                // println!("\nSTATE VEC: \n{:#?}", state_vec);
                trans_stack.push(state_vec_to_expr(&state_vec));
                state_vec = Vec::new();
                // value;
                state_vec.push(state_map.clone())
            // }
        }
        prev_id_value = curr_id_value;
    }

    trans_stack.push(state_vec_to_expr(&state_vec));
    // println!("\nAFTER FOR LOOP STATE VEC: \n {:#?}", state_vec);
    // println!("TRANS STACK: {:?}", trans_stack);
    // let transitions: Box<Expression> = combine_expr(trans_stack);
    // println!("{:?}", transitions);

    Ok(())
}

// given a variable and its state write correct expression
fn state_to_expr(var_name: &str, state: &str, next : bool, max_bit_map: &HashMap<String, i32>) -> Box<Expression> {
    let name;
    if next {
        name = format!("{}'", var_name);
    } else {
        name = var_name.to_string();
    }

    // TODO: eventually match more but good for mini.smv
    match state {
        "TRUE" => {
            Box::new(Expression::Literal(Literal::Atom(name.to_string())))
        }
        "FALSE" => {
            Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom(name.to_string())))))
        } 
        // integer value
        _ => 
            if let Ok(_) = state.parse::<i32>() {
                // Handle the integer case, for example, creating a different expression
                let state_num: i32 = state.parse().expect("REASON"); // string to int
                match max_bit_map.get(var_name) {
                    Some(max_bit) => blast_bits(var_name, state_num, *max_bit, next),
                    None => panic!("No max_bit found for '{}'.", var_name),
                }
                // blast_bits(var_name, state_num, 6, next) // TODO: hardcoded, need to find a way to get max bit 
            } else {
                unreachable!("Should not have gotten here");
            }   
    }
}

fn state_vec_to_expr(state_vec: &Vec<StateMap>) -> Box<Expression>{
    let mut all_initial: HashSet<Box<Expression>> = HashSet::new();
    let mut all_next: HashSet<Box<Expression>> = HashSet::new();
    
    // go through vec of state maps
    for map in state_vec {
        // println!{"\nSTATE MAP: {:?}", map};
        // collect all initial and next states for a state map
        let initial_states: Vec<Box<Expression>> = map.collect_all_initial_states().into_iter().collect();
        let next_states: Vec<Box<Expression>> = map.collect_all_next_states().into_iter().collect();

        // combine initial and next states

        // let mut combined_init: Box<Expression> = Box::new(Expression::Literal(Literal::Atom("STATE_VEC_BUG".to_string())));
        // let mut combined_next: Box<Expression> = Box::new(Expression::Literal(Literal::Atom("STATE_VEC_BUG".to_string())));
        
        // if initial is only one element, no need for AND gate
        let combined_init = if initial_states.len() < 2 {
            initial_states[0].clone() 
        // } else if initial_states.len() == 2 {
        //     combined_init = Box::new(Expression::And(initial_states[0].clone(), initial_states[1].clone()));
        } else {
            Box::new(Expression::MAnd(initial_states))
        };

        let combined_next = if next_states.len() < 2 {
            next_states[0].clone() 
        // } else if next_states.len() == 2 {
        //     combined_next = Box::new(Expression::And(next_states[0].clone(), next_states[1].clone()));
        } else {
            Box::new(Expression::MAnd(next_states))
        };
        // let combined_init: Box<Expression> = Box::new(Expression::MAnd(initial_states));
        // let combined_next: Box<Expression> = Box::new(Expression::MAnd(next_states));


        // println!("COMBINED INIT: {:?}", combined_init);
        // println!("COMBINED NEXT: {:?}", combined_next);


        all_initial.insert(combined_init);
        all_next.insert(combined_next);
    }

    // println!("\nALL_INITIAL: {:?}", all_initial);
    // println!("\nALL_NEXT: {:?}", all_next);

    let mut lhs: Box<Expression> = Box::new(Expression::Literal(Literal::Atom("STATE_VEC_TO_EXPR_BUG".to_string()))); 
    let mut rhs: Box<Expression> = Box::new(Expression::Literal(Literal::Atom("STATE_VEC_TO_EXPR_BUG".to_string())));

    // if all_initial or all_next is only 1 element
    if all_initial.len() < 2 {
        if let Some(&ref element) = all_initial.iter().next() {
            lhs = element.clone(); // get only element in hash set
        } 
    } else {
        lhs = Box::new(Expression::MOr(all_initial.iter().cloned().collect()));
    }

    if all_next.len() < 2 {
        if let Some(&ref element) = all_next.iter().next() {
            rhs = element.clone(); // get only element in hash set
        } 
    } else {
        rhs = Box::new(Expression::MOr(all_next.iter().cloned().collect()));
    }

    // println!("\nLHS: {:?}", lhs);
    // println!("\nRHS: {:?}", rhs);

    let negate_lhs = Box::new(Expression::Neg(lhs.clone()));
    let full_expr = Box::new(Expression::Or(negate_lhs, rhs)); // initial -> next

    // println!("FULL EXPR: {:?}", full_expr);

    return full_expr;
}

// fn map_to_expr(state_map: &StateMap) -> Box<Expression> {

//     let initial_states: Vec<Box<Expression>> = state_map.collect_all_initial_states().into_iter().collect();
//     let next_states: Vec<Box<Expression>> = state_map.collect_all_next_states().into_iter().collect();

//     // println!("{:?}", initial_states);
//     // println!("{:?}", next_states);

//     // let mut combined_init: Box<Expression> = Box::new(Expression::Literal(Literal::Atom("".to_string())));
//     // let mut combined_next: Box<Expression> = Box::new(Expression::Literal(Literal::Atom("".to_string())));

//     let combined_init: Box<Expression> = Box::new(Expression::MAnd(initial_states));
//     let combined_next: Box<Expression> = Box::new(Expression::MAnd(next_states));

//     // // TODO: make this a function
//     // if initial_states.len() > 1 {
//     //     for i in 0..initial_states.len() {
//     //         if i == 0 {
//     //             combined_init = initial_states[i].clone();
//     //         } else {
//     //             combined_init = Box::new(Expression::And(initial_states[i].clone(), combined_init.clone()));
//     //         } 
//     //     }
//     // } else {
//     //     combined_init = initial_states[0].clone();
//     // }

//     // if next_states.len() > 1 {
//     //     for i in 0..next_states.len() {
//     //         if i == 0 {
//     //             combined_next = next_states[i].clone();
//     //         } else {
//     //             combined_next = Box::new(Expression::And(next_states[i].clone(), combined_next.clone()));
//     //         } 
//     //     }
//     // } else {
//     //     combined_next = next_states[0].clone();
//     // }

//     // println!("COMBINED INIT: {:?}", combined_init);
//     // println!("COMBINED NEXT: {:?}", combined_next);

//     let negate_init = Box::new(Expression::Neg(combined_init));
//     let full_expr = Box::new(Expression::Or(negate_init, combined_next)); // initial -> next

//     // let expr1 = Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom("a".to_string())))));
//     // let expr2 = Box::new(Expression::Literal(Literal::Atom("b".to_string())));
//     // let res1 = Box::new(Expression::Or(expr1,expr2)); // a -> b

//     return full_expr

// }

fn combine_expr(trans_stack : Vec<Box<Expression>>) -> Box<Expression> {

    // initialized with random value bc won't let me return if it is uninitialized
    if trans_stack.len() > 1 {
        let combined_expr: Box<Expression> = Box::new(Expression::MAnd(trans_stack));
        return combined_expr;
    } else {
        return trans_stack[0].clone();
    }
    // println!("size: {:?}", trans_stack.len());
    // for i in 0..trans_stack.len() {
    //     // println!("expression: {:?}", trans_stack[i]);
        
    //     if i == 0 {
    //         combined_expr = trans_stack[i].clone();
    //     } else {
    //         combined_expr = Box::new(Expression::And(trans_stack[i].clone(), combined_expr.clone()));
    //     }  
    // }
    // return combined_expr
}

// var_name: variable name e.g. "PC"
// state: int value of PC
// max_b: max bit for blasted var
// next: true if var is a next var
fn blast_bits(var_name: &str, state_num: i32, max_b: i32, next: bool) -> Box<Expression> {
    let mut bit_order = 0;
    let mut max_bit_order = 0;
    let mut bit_vector: Vec<Box<Expression>> = Vec::new();
    let mut bit = String::new();
    let mut max_bit = String::new();
    let mut var ;
    let mut state = state_num.clone();
    let mut max = max_b.clone();
    
    while state != 0 {
        let r = if state % 2 == 0 { "0" } else { "1" };
        if next {
            var = format!("{}[{}]'", var_name, bit_order);
        } else {
            var = format!("{}[{}]", var_name, bit_order);
        }
        if r == "0" {
            bit_vector.push(Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom(var.to_string()))))));
        } else {
            bit_vector.push(Box::new(Expression::Literal(Literal::Atom(var.to_string()))));
        }
        bit = format!("{}{}", r, bit);
        state /= 2;
        bit_order += 1;
    }
    
    while max != 0 {
        let max_r = if max % 2 == 0 { "0" } else { "1" };
        max_bit = format!("{}{}", max_r, max_bit);
        max /= 2;
        max_bit_order += 1;
    }
    
    while max_bit_order != bit_order {
        if next {
            var = format!("{}[{}]'", var_name, bit_order);
        } else {
            var = format!("{}[{}]", var_name, bit_order);
        }
        bit_vector.push(Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom(var.to_string()))))));
        bit_order += 1;
    }
    
    // bit_vector.reverse();
    // bit_vector
    // let mut blasted_var: Box<Expression> = Box::new(Expression::Literal(Literal::Atom("".to_string())));
    let blasted_var: Box<Expression> = Box::new(Expression::MAnd(bit_vector));

    // for i in 0..bit_vector.len() {
    //     // println!("expression: {:?}", trans_stack[i]);
    //     if i == 0 {
    //         blasted_var = bit_vector[i].clone();
    //     } else {
    //         blasted_var = Box::new(Expression::And(bit_vector[i].clone(), blasted_var.clone()));
    //     }  
    // }
    // println!("BLASTED VAR: {:?}", blasted_var);

    return blasted_var;
}

// #[test]
// fn test_blasted_var(){
//     let var_name = "PC";
//     let state_num = 1;
//     let max_b = 1;
//     let next = false;
//     println!("{:?}", expression);
//     let blasted_var = blast_bits(var_name, state_num, max_b: i32, next: bool);
//     assert_eq!(blasted_var, Box::new(Expression::G(Box::new(Expression::Literal(Literal::Atom("a".to_string()))))));
// }