use std::env;
use std::fs::File;
use std::path::{PathBuf};
use crate::input_to_expressions::input_to_expression;
use crate::parser::Parser;
use crate::symbol_map::SymbolMap;
use logging::{Logger};
use crate::create_gates_from_cdf;

/// Function to replace the last occurrence of one string with another
pub fn replace_last_occurrence(atom: &str, target: &str, replacement: &str) -> String {
    if let Some(idx) = atom.rfind(target) {
        let mut result = String::with_capacity(atom.len() + replacement.len() - target.len());
        result.push_str(&atom[..idx]);
        result.push_str(replacement);
        result.push_str(&atom[idx + target.len()..]);
        result
    } else {
        atom.to_string()
    }
}

/// Function creates a file at the path outputs/{file}, displays error reason if it can't
pub fn create_file() -> File {
    let file = "HQ.qcir";
    // try to create a file at currentdir/outputs/{file}. assume outputs folder already exists
    let path = env::current_dir();
    let mut path = path.expect("REASON");
    while path.ends_with("HyperRust"){ // NOTE!!!! This is a hack to get the path to the root of the project, ROOT MUST BE HyperRust!
        path = PathBuf::from(path.parent().expect("Should have a parent"));
    }

    let path = path.join("outputs").join(file);
    std::fs::create_dir_all(path.parent().unwrap()).expect("Failed to create output directory");

    let display = path.display();
    let file = match File::create(&path) {
        Err(why) => panic!("couldn't create {}: {}", display, why),
        Ok(file) => file,
    };
    return file;
}

/// function to help format the output string
/// It gets the footer, the header, as well as ANDing the models together
fn get_string_quantifiers_and_ends(
    model_map: &Vec<(String, i32)>, 
    quantifiers: &Vec<(String,String)>, 
    logger: &Logger, 
    symbol_map: &mut SymbolMap) -> (String, String, Vec<String>) {
    let output_string = &mut String::new();
    let ending_headers = &mut String::new();
    let final_ands = &mut Vec::new();
    let mut counter = 0;
    let debug = logger.get_mode();
    let mut initial_states;
    while  counter < model_map.len() as i32{
        // *********** Assign variables ***********
        initial_states = symbol_map.get_initials(&counter);
        let map_string = &mut String::new();
        let mut symbol_map_vec: Vec<(&String, &i32)> = symbol_map.get_symbol_map(&counter).iter().collect();
        let (semantic, _) = quantifiers[counter as usize].clone();
        symbol_map_vec.sort_by(|a, b| a.1.cmp(b.1));
        let layer1_constants = &mut String::new();

        // *********** Gets the header and quantifiers ***********
        for (key, value) in symbol_map_vec {
            if debug {
                map_string.push_str(&format!("{}]", replace_last_occurrence(key, "_", "[")));
            } else {
                map_string.push_str(&*value.to_string());
            }
            // split the first character from the rest of the string, not it can be be dynamic size.
            // split on the last _ of the key
            let idk = key.rfind("_").unwrap();
            let mut l_key = key[..idk].to_string();
            let r_key = key[idk+1..].to_string();

            // *********** Ending Headers *************
            map_string.push_str(",");
            let infix: String;
            if counter == 0 {
                infix = "_A".parse().unwrap();
            } else {
                infix = "_B".parse().unwrap();
            }
            ending_headers.push_str(&format!("# {} : {}{}[{}]\n", value, l_key,infix,r_key));

            // *********** This loop will get the semantic gates ***********
            // if the last two characters of the key are _0, then it is an initial state
            if key.ends_with("_0") {

                // strip to just its letter value
                // get rid of last 2 letters
                let key = key.split_at(key.len()-2).0;
                if !initial_states.contains(&key.to_owned()){
                    l_key = format!("-{}", l_key);
                    if debug{
                        layer1_constants.push_str(&format!("{}[{}],", l_key, r_key));
                    }else{
                        layer1_constants.push_str(&format!("-{},", value));
                    }

                } else{
                    if debug{
                        layer1_constants.push_str(&format!("{}[{}],", l_key, r_key));
                    }else{
                        layer1_constants.push_str(&format!("{},", value));
                    }
                }
            }
        }
        logger.log(&*format!("Layer 1 constants: {}", layer1_constants.to_string().trim_end_matches(",").to_string()), 1);
        final_ands.push(layer1_constants.to_string().trim_end_matches(",").to_string());
        output_string.push_str(&format!("{}({})\n", semantic,map_string.trim_end_matches(",")));
        counter += 1;


    }
    return (format!("#QCIR-G14\n{}", output_string), ending_headers.to_owned(), final_ands.to_owned());
}

pub fn get_output_string(model_map: &Vec<(String, i32)>,max_gate_number: i32, logger: &Logger, formula: &str, quantifiers: &Vec<(String,String)>, semantics: &String, layers: i32, symbol_map: &mut SymbolMap) -> String {

    
    // Beginning and end of the output string
    let (starting_header,footer,final_ands) = get_string_quantifiers_and_ends(model_map, quantifiers, logger, symbol_map); 
    // println!("??? {}", starting_header);
    // has the header and quantifiers
    let debug = logger.get_mode();
    // Middle part of the output string
    let middle_string = &mut String::new();
    let mut counter = 0;
    let mut and_max_gate = max_gate_number.clone();
    let model_outputs = &mut String::new();

    // TODO: the initial gate is buggy
    for (model_output, model_max_gate_number) in model_map {
        // This gets the ands for the model. It should be initials AND its out put from right
        model_outputs.push_str(&*model_output);
        let layer_and = &mut String::new();
        if debug{
            layer_and.push_str(&*format!("g{} = and({},g{})\n", and_max_gate + 1,final_ands[counter], model_max_gate_number));
        } else{
            layer_and.push_str(&*format!("{} = and({},{})\n", and_max_gate + 1,final_ands[counter], model_max_gate_number));
        }

        middle_string.push_str(&layer_and);
        counter += 1;
        and_max_gate += 1;
    }


    // This is the model gates. If it is exists then gate + n = and(current model, gate + n-1)
    // and next model is recursive. so if next model has forall, then it becomes gate + n-1 = or(not(next model), gate +n-2)
    // we set the variables now, so that we can use them later. We add them after the LTL formula

    let mut model_output_gate = max_gate_number.clone()+1; // we are going to count backwards so that the output gate is last


    // Now for the LTL formula part
    // Now do the parsing of the ltl part
    let expression = input_to_expression(formula);
    logger.log("LTL formula to expression tree", 2);
    logger.log(&*format!("Gate being input to formula parsing: {:?}", and_max_gate), 1);

    let mut parser = Parser::new(expression, symbol_map, debug, layers, and_max_gate.clone(), (*semantics.clone()).to_owned(), (*logger).clone());
    let (output, gate, negated) = parser.ltl_parser();
    middle_string.push_str(output.as_str());
    // println!("----------\nGate is: {}\n----------", gate);
    // Here we do the model gates so M1/\M2->phi is exists M1, forall M2, phi
    let mut last_and = &mut String::new();
    let mut quantifier_output_gate = gate+quantifiers.len() as i32;
    // THH: patch: avoid forward referencing
    let mut bmc = "".to_string();
    for (quantifier, _) in quantifiers {
        let mut temp = quantifier_output_gate -1;
        // println!("{}", negated);
        if (temp == gate) & negated{ // if its the last quantifier in the loop and the parser ended with a negation
            temp = 0-temp
        }

        if quantifier == "Exists" {
            if debug{
                last_and.push_str(&format!("g{} = and(g{},g{})\n", quantifier_output_gate, model_output_gate, temp));
            } else{
                // last_and.push_str(&format!("{} = and({},{})\n", quantifier_output_gate, model_output_gate, temp));
                // THH: patch: avoid forward referencing
                bmc = (&format!("{} = and({},{})\n", quantifier_output_gate, model_output_gate, temp)).to_owned() + &bmc;
            }
        } else if quantifier == "Forall"  {
            if debug{
                last_and.push_str(&format!("g{} = or(-g{},g{})\n", quantifier_output_gate, model_output_gate, temp));
            } else{
                // last_and.push_str(&format!("{} = or(-{},{})\n", quantifier_output_gate, model_output_gate, temp));
                // THH: patch: avoid forward referencing
                bmc = (&format!("{} = or(-{},{})\n", quantifier_output_gate, model_output_gate, temp)).to_owned() + &bmc;
            }
        }
        model_output_gate += 1;
        quantifier_output_gate -= 1;
    }
    // trim last comma
    // let mut binding = last_and.trim_end_matches(",").to_string();
    // THH: patch: avoid forward referencing
    let mut binding = bmc.trim_end_matches(",").to_string();
    last_and = &mut binding;
    middle_string.push_str(&last_and);


    // Now combine all parts
    let mut output_string = String::new();

    // HEADER
    output_string.push_str(&starting_header);

    // OUTPUT
    if debug{
        output_string.push_str(format!("output(g{})\n", gate + quantifiers.len() as i32).as_str());
    } else{
        output_string.push_str(format!("output({})\n", gate + quantifiers.len() as i32).as_str());
    }

    // LOGICAL GATES
    output_string.push_str(&model_outputs);
    output_string.push_str("### Middle\n");
    output_string.push_str(&middle_string);
    output_string.push_str("### Footer\n");
    output_string.push_str(&footer);

    return output_string;
}

/// Gets the output_string for the encoding version of the tool.
/// This is the same as the original but alters the headers slightly for the new helper variables
pub fn get_output_string_encoding_version(model_map: &Vec<(String, i32)>,max_gate_number: i32, logger: &Logger, formula: &str, quantifiers: &Vec<(String,String)>, semantics: &String, layers: i32, symbol_map: &mut SymbolMap) -> String {
    // Beginning and end of the output string
    let (starting_header,footer,final_ands) = get_string_quantifiers_and_ends_encoding_version(model_map, quantifiers, logger, symbol_map); // has the header and quantifiers
    let debug = logger.get_mode();
    // Middle part of the output string
    let middle_string = &mut String::new();
    let mut counter = 0;
    let mut and_max_gate = max_gate_number.clone();
    let model_outputs = &mut String::new();
    for (model_output, model_max_gate_number) in model_map {
        // This gets the ands for the model. It should be initials AND its out put from right
        model_outputs.push_str(&*model_output);
        let layer_and = &mut String::new();
        if debug{
            layer_and.push_str(&*format!("g{} = and({},g{})\n", and_max_gate + 1,final_ands[counter], model_max_gate_number));
        } else{
            layer_and.push_str(&*format!("{} = and({},{})\n", and_max_gate + 1,final_ands[counter], model_max_gate_number));
        }

        middle_string.push_str(&layer_and);
        counter += 1;
        and_max_gate += 1;
    }


    // This is the model gates. If it is exists then gate + n = and(current model, gate + n-1)
    // and next model is recursive. so if next model has forall, then it becomes gate + n-1 = or(not(next model), gate +n-2)
    // we set the variables now, so that we can use them later. We add them after the LTL formula

    let mut model_output_gate = max_gate_number.clone()+1; // we are going to count backwards so that the output gate is last

    // Now for the LTL formula part
    // Now do the parsing of the ltl part
    let expression = input_to_expression(formula);
    logger.log("LTL formula to expression tree", 2);
    logger.log(&*format!("Gate being input to formula parsing: {:?}", and_max_gate), 1);

    let mut parser = Parser::new(expression, symbol_map, debug, layers, and_max_gate.clone(), (*semantics.clone()).to_owned(), (*logger).clone());
    let (output, gate, negated) = parser.ltl_parser();
    middle_string.push_str(output.as_str());
    // println!("----------\nGate is: {}\n----------", gate);
    // Here we do the model gates so M1/\M2->phi is exists M1, forall M2, phi
    let mut last_and = &mut String::new();
    let mut quantifier_output_gate = gate+quantifiers.len() as i32;
    // THH: patch: avoid forward referencing
    let mut bmc = "".to_string();
    for (quantifier, _) in quantifiers {
        let mut temp = quantifier_output_gate -1;
        // println!("{}", negated);
        if (temp == gate) & negated{ // if its the last quantifier in the loop and the parser ended with a negation
            temp = 0-temp
        }

        if quantifier == "Exists" {
            if debug{
                last_and.push_str(&format!("g{} = and(g{},g{})\n", quantifier_output_gate, model_output_gate, temp));
            } else{
                // last_and.push_str(&format!("{} = and({},{})\n", quantifier_output_gate, model_output_gate, temp));
                bmc = (&format!("{} = and({},{})\n", quantifier_output_gate, model_output_gate, temp)).to_owned() + &bmc;
            }
        } else {
            if debug{
                last_and.push_str(&format!("g{} = or(-g{},g{})\n", quantifier_output_gate, model_output_gate, temp));
            } else{
                // last_and.push_str(&format!("{} = or(-{},{})\n", quantifier_output_gate, model_output_gate, temp));
                bmc = (&format!("{} = or(-{},{})\n", quantifier_output_gate, model_output_gate, temp)).to_owned() + &bmc;
            }
        }
        model_output_gate += 1;
        quantifier_output_gate -= 1;
    }
    // trim last comma
    // let mut binding = last_and.trim_end_matches(",").to_string();
    // THH: patch: avoid forward referencing
    let mut binding = bmc.trim_end_matches(",").to_string();
    last_and = &mut binding;
    middle_string.push_str(&last_and);


    // Now combine all parts
    let mut output_string = String::new();
    output_string.push_str(&starting_header);
    if debug{
        output_string.push_str(format!("output(g{})\n", gate + quantifiers.len() as i32).as_str());
    } else{
        output_string.push_str(format!("output({})\n", gate + quantifiers.len() as i32).as_str());
    }
    output_string.push_str(&model_outputs);
    output_string.push_str(&middle_string);
    output_string.push_str(&footer);

    return output_string;
}

/// function to help format the output string
/// It gets the footer, the header, as well as ANDing the models together
/// Slightly changes headers from the original function
fn get_string_quantifiers_and_ends_encoding_version(model_map: &Vec<(String, i32)>, quantifiers: &Vec<(String,String)>, logger: &Logger, symbol_map: &mut SymbolMap) -> (String, String, Vec<String>) {
    let output_string = &mut String::new();
    let ending_headers = &mut String::new();
    let final_ands = &mut Vec::new();
    let mut counter = 0;
    let debug = logger.get_mode();
    let mut initial_states;
    while  counter < model_map.len() as i32{
        // *********** Assign variables ***********
        initial_states = symbol_map.get_initials(&counter);
        let map_string = &mut String::new();
        let helper_map_string = &mut String::new();
        let mut symbol_map_vec: Vec<(&String, &i32)> = symbol_map.get_symbol_map(&counter).iter().collect();
        let (semantic, _) = quantifiers[counter as usize].clone();
        symbol_map_vec.sort_by(|a, b| a.1.cmp(b.1));
        let layer1_constants = &mut String::new();

        // *********** Gets the header and quantifiers ***********
        for (key, value) in symbol_map_vec {
            if key.contains("_helper_"){
                if debug {
                    helper_map_string.push_str(&format!("{}]", replace_last_occurrence(key, "_", "[")));
                } else {
                    helper_map_string.push_str(&*value.to_string());
                }
                helper_map_string.push_str(",");
            }else {
                if debug {
                    map_string.push_str(&format!("{}]", replace_last_occurrence(key, "_", "[")));
                } else {
                    map_string.push_str(&*value.to_string());
                }
                map_string.push_str(",");
            }

            // split the first character from the rest of the string, not it can be be dynamic size.
            // split on the last _ of the key
            let idk = key.rfind("_").unwrap();
            let mut l_key = key[..idk].to_string();
            let r_key = key[idk+1..].to_string();

            // *********** Ending Headers *************

            let infix: String;
            if counter == 0 {
                infix = "_A".parse().unwrap();
            } else {
                infix = "_B".parse().unwrap();
            }
            ending_headers.push_str(&format!("# {} : {}{}[{}]\n", value, l_key,infix,r_key));

            // *********** This loop will get the semantic gates ***********
            // if the last two characters of the key are _0, then it is an initial state
            if key.ends_with("_0") & (!key.contains("_helper")) {
                // strip to just its letter value
                // get rid of last 2 letters
                let key = key.split_at(key.len()-2).0;
                if !initial_states.contains(&key.to_owned())  & !key.contains("_helper_"){
                    l_key = format!("-{}", l_key);
                    if debug{
                        layer1_constants.push_str(&format!("{}[{}],", l_key, r_key));
                    }else{
                        layer1_constants.push_str(&format!("-{},", value));
                    }

                } else{
                    if debug{
                        layer1_constants.push_str(&format!("{}[{}],", l_key, r_key));
                    }else{
                        layer1_constants.push_str(&format!("{},", value));
                    }
                }
            }
        }
        logger.log(&*format!("Layer 1 constants: {}", layer1_constants.to_string().trim_end_matches(",").to_string()), 1);
        final_ands.push(layer1_constants.to_string().trim_end_matches(",").to_string());
        output_string.push_str(&format!("{}({})\n", semantic,map_string.trim_end_matches(",")));
        if semantic == "Forall"{
            output_string.push_str(&format!("{}({})\n", "Exists",helper_map_string.trim_end_matches(",")));
        } else {
            output_string.push_str(&format!("{}({})\n", "Forall",helper_map_string.trim_end_matches(",")));
        }
        counter += 1;


    }
    return (format!("#QCIR-G14\n{}", output_string), ending_headers.to_owned(), final_ands.to_owned());
}

/// Gets the output_string for the encoding version of the tool.
/// This is the same as the original but alters the headers slightly for the new helper variables
pub fn get_output_string_unified(model_map: &Vec<(String, i32)>, mut max_gate_number: i32, logger: &Logger, formula: &str, quantifiers: &Vec<(String, String)>, semantics: &String, layers: i32, symbol_map: &mut SymbolMap, model_bool: bool, model_flag: &String) -> String {
    // Beginning and end of the output string
    let (starting_header,footer, mut final_ands) = get_string_quantifiers_and_ends_unified(model_map, quantifiers, logger, symbol_map, model_bool, model_flag); // has the header and quantifiers
    // TODO: Here should be the new final_ands function call. It should build the and gates for the initial values
    // My thought is to use the gate_builder to build the gates. It does the or/and for us. Easy to reuse.
    let mut counter = 0;
    // let mut final_ands: Vec<String> = Vec::new();
    let mut final_ands_string = String::new();
    while  counter < model_map.len() as i32 {
        symbol_map.model = counter;
        let expression = symbol_map.get_initial_expression(&counter);
        let(string,gate,conj) = create_gates_from_cdf(&*expression, logger, max_gate_number, 1, symbol_map);
        final_ands.push(conj[0].to_string());
        max_gate_number = gate;
        final_ands_string.push_str(&string);

        counter += 1;
    }
    // println!("Final ands: {:?}", final_ands);
    // println!("Final ands string: {:?}", final_ands_string);
    // println!("Max gate number: {:?}", max_gate_number);
    /*
    78 = and(-7,-10)
    79 = and(-37,-32)
    80 = and(-7,-10,31)
    81 = and(-32,-37,77)
     */

    let debug = logger.get_mode();
    // Middle part of the output string
    let middle_string = &mut String::new();
    middle_string.push_str(&final_ands_string);
    let mut counter = 0;
    let mut and_max_gate = max_gate_number.clone();
    let model_outputs = &mut String::new();
    for (model_output, model_max_gate_number) in model_map {
        // This gets the ands for the model. It should be initials AND its out put from right
        model_outputs.push_str(&*model_output);
        let layer_and = &mut String::new();
        if debug{
            layer_and.push_str(&*format!("g{} = and({},g{})\n", and_max_gate + 1,final_ands[counter], model_max_gate_number));
        } else{
            layer_and.push_str(&*format!("{} = and({},{})\n", and_max_gate + 1,final_ands[counter], model_max_gate_number));
        }

        middle_string.push_str(&layer_and);
        counter += 1;
        and_max_gate += 1;
    }


    // This is the model gates. If it is exists then gate + n = and(current model, gate + n-1)
    // and next model is recursive. so if next model has forall, then it becomes gate + n-1 = or(not(next model), gate +n-2)
    // we set the variables now, so that we can use them later. We add them after the LTL formula

    let mut model_output_gate = max_gate_number.clone()+1; // we are going to count backwards so that the output gate is last

    // Now for the LTL formula part
    // Now do the parsing of the ltl part
    let expression = input_to_expression(formula);
    logger.log("LTL formula to expression tree", 2);
    logger.log(&*format!("Gate being input to formula parsing: {:?}", and_max_gate), 1);

    let mut parser = Parser::new(expression, symbol_map, debug, layers, and_max_gate.clone(), (*semantics.clone()).to_owned(), (*logger).clone());
    let (output, gate, negated) = parser.ltl_parser();
    middle_string.push_str(output.as_str());

    // println!("----------\nGate is: {}\n----------", gate);
    // Here we do the model gates so M1/\M2->phi is exists M1, forall M2, phi
    let mut last_and = &mut String::new();
    let mut quantifier_output_gate = gate+quantifiers.len() as i32;
    // THH: patch: avoid forward referencing
    let mut bmc = "".to_string();
    
    for (quantifier, _) in quantifiers {
        let mut temp = quantifier_output_gate -1;
        // println!("{}", negated);
        if (temp == gate) & negated{ // if its the last quantifier in the loop and the parser ended with a negation
            temp = 0-temp
        }

        if quantifier == "Exists" {
            if debug{
                last_and.push_str(&format!("g{} = and(g{},g{})\n", quantifier_output_gate, model_output_gate, temp));
            } else{
                // last_and.push_str(&format!("{} = and({},{})\n", quantifier_output_gate, model_output_gate, temp));
                // THH: patch: avoid forward referencing
                bmc = (&format!("{} = and({},{})\n", quantifier_output_gate, model_output_gate, temp)).to_owned() + &bmc;
            }
        } else {
            if debug{
                last_and.push_str(&format!("g{} = or(-g{},g{})\n", quantifier_output_gate, model_output_gate, temp));
            } else{
                // last_and.push_str(&format!("{} = or(-{},{})\n", quantifier_output_gate, model_output_gate, temp));
                // THH: patch: avoid forward referencing
                bmc = (&format!("{} = or(-{},{})\n", quantifier_output_gate, model_output_gate, temp)).to_owned() + &bmc;
            }
        }
        model_output_gate += 1;
        quantifier_output_gate -= 1;
    }
    // trim last comma
    // let mut binding = last_and.trim_end_matches(",").to_string();
    // THH: patch: avoid forward referencing
    let mut binding = bmc.trim_end_matches(",").to_string();
    last_and = &mut binding;
    middle_string.push_str(&last_and);
    // THH: patch: avoid forward referencing
    // let mut binding = bmc.trim_end_matches(",").to_string();

    // Now combine all parts
    let mut output_string = String::new();
    output_string.push_str(&starting_header);
    if debug{
        output_string.push_str(format!("output(g{})\n", gate + quantifiers.len() as i32).as_str());
    } else{
        output_string.push_str(format!("output({})\n", gate + quantifiers.len() as i32).as_str());
    }
    output_string.push_str(&model_outputs);
    output_string.push_str(&middle_string);
    output_string.push_str(&footer);

    return output_string;
}


/// function to help format the output string
/// It gets the footer, the header, as well as ANDing the models together
/// Slightly changes headers from the original function
fn get_string_quantifiers_and_ends_unified(model_map: &Vec<(String, i32)>, quantifiers: &Vec<(String,String)>, logger: &Logger, symbol_map: &mut SymbolMap, model_bool: bool, model_flag: &String) -> (String, String, Vec<String>) {
    let output_string = &mut String::new();
    let ending_headers = &mut String::new();
    let final_ands = &mut Vec::new();
    let mut counter = 0;
    let debug = logger.get_mode();
    let mut initial_states;
    while  counter < model_map.len() as i32{
        // *********** Assign variables ***********
        initial_states = symbol_map.get_initials(&counter);
        let map_string = &mut String::new();
        let helper_map_string = &mut String::new();
        let mut symbol_map_vec: Vec<(&String, &i32)> = symbol_map.get_symbol_map(&counter).iter().collect();
        let (semantic, _) = quantifiers[counter as usize].clone();
        symbol_map_vec.sort_by(|a, b| a.1.cmp(b.1));
        let layer1_constants = &mut String::new();

        // *********** Gets the header and quantifiers ***********
        for (key, value) in symbol_map_vec {
            if key.contains("_helper_"){
                if debug {
                    helper_map_string.push_str(&format!("{}]", replace_last_occurrence(key, "_", "[")));
                } else {
                    helper_map_string.push_str(&*value.to_string());
                }
                helper_map_string.push_str(",");
            }else {
                if debug {
                    map_string.push_str(&format!("{}]", replace_last_occurrence(key, "_", "[")));
                } else {
                    map_string.push_str(&*value.to_string());
                }
                map_string.push_str(",");
            }

            // split the first character from the rest of the string, not it can be be dynamic size.
            // split on the last _ of the key
            let idk = key.rfind("_").unwrap();
            let mut l_key = key[..idk].to_string();
            let r_key = key[idk+1..].to_string();

            // *********** Ending Headers *************

            let infix: String;
            if counter == 0 {
                infix = "_A".parse().unwrap();
            } else {
                infix = "_B".parse().unwrap();
            }
            ending_headers.push_str(&format!("# {} : {}{}[{}]\n", value, l_key,infix,r_key));

            // *********** This loop will get the semantic gates ***********
            // if the last two characters of the key are _0, then it is an initial state
            if key.ends_with("_0") & (!key.contains("_helper")) {
                // strip to just its letter value
                // get rid of last 2 letters
                let key = key.split_at(key.len()-2).0;
                if !initial_states.contains(&key.to_owned())  & !key.contains("_helper_"){
                    l_key = format!("-{}", l_key);
                    if debug{
                        layer1_constants.push_str(&format!("{}[{}],", l_key, r_key));
                    }else{
                        layer1_constants.push_str(&format!("-{},", value));
                    }

                } else{
                    if debug{
                        layer1_constants.push_str(&format!("{}[{}],", l_key, r_key));
                    }else{
                        layer1_constants.push_str(&format!("{},", value));
                    }
                }
            }
        }
        logger.log(&*format!("Layer 1 constants: {}", layer1_constants.to_string().trim_end_matches(",").to_string()), 1);
        final_ands.push(layer1_constants.to_string().trim_end_matches(",").to_string());
        output_string.push_str(&format!("{}({})\n", semantic,map_string.trim_end_matches(",")));

        // Check if the model is one of the ones we are encoding. model flag is the name of the model we are encoding
        // NOTE: odd logic here because the short circuiting wasn't working
        // (model_bool & model_flag.is_empty()) | (model_bool & (counter == *symbol_map.get_model_number_from_name(model_flag)))
        // is what this is building

        let mut truth = model_bool & model_flag.is_empty();
        if truth == false{
            truth = model_bool & (counter == *symbol_map.get_model_number_from_name(model_flag));
        }
        if truth {
            if semantic == "Forall"{
                output_string.push_str(&format!("{}({})\n", "Exists",helper_map_string.trim_end_matches(",")));
            } else {
                output_string.push_str(&format!("{}({})\n", "Forall",helper_map_string.trim_end_matches(",")));
            }
        }

        counter += 1;


    }
    // println!("Broke where we thought?");
    return (format!("#QCIR-G14\n{}", output_string), ending_headers.to_owned(), final_ands.to_owned());
}
