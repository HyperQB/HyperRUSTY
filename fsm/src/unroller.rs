use crate::gate_builder::create_gates_from_cdf;
use std::io::Write;
use crate::symbol_map::SymbolMap;
use expressions::*;
use logging::{Logger};
use crate::input_to_expressions::{input_to_expression, input_to_expression_optimized};


/// Legacy unrolling
/// # Arguments
/// * `expression`: The pairs of initial states and expressions
/// * `layers`: The number of times to unwrap the expression
/// * `debug`: Whether to print the fsm
/// * `quantifiers`: The quantifiers for the model
/// * `semantics`: The semantics for the model
/// * `logger`: The logger
/// * `formula`: The formula for the models
pub fn legacy_unwrap(   expression: Vec<(String,String)>, 
                        formula: &str, 
                        layers: i32, 
                        logger: &Logger, 
                        quantifiers: &Vec<(String,String)>,
                        semantics: &String) 
{
    let mut symbol_map = SymbolMap::new(expression.len() as i32, layers);
    symbol_map.setup_model_map(quantifiers);
    let mut model_map: Vec<(String, i32)> = Vec::new();
    let max_gate_number = 0;
    // let mut conjunction_list: Vec<i32>;
    // let mut output_str = String::new();

    for (initial, transitions) in expression {
        // println!("\nINIT:  {}", initial);

        // println!("\nTRANS: {}", transitions);

        // println!("quantifiers = {:?}", quantifiers);

        symbol_map.add_initials(&initial);
        logger.log("Starting input to expression", 1);
        let fsm = input_to_expression(&transitions);

        //logger.log(&*format!("The fsm is: {:?}", fsm), 1);
        // output is (output_string, max_gate_number, symbol_map) for that model
        logger.log("Starting create gates from cdf", 1);
        let (output_str, max_gate_number, _conjunction_list) = create_gates_from_cdf(&fsm, logger, max_gate_number, layers, &mut symbol_map);
        symbol_map.model += 1;
        model_map.push((output_str, max_gate_number));

        // now drop fsm to save memory
        logger.log("Starting mem drop:", 1);
        logger.log("Dropping fsm", 1);
        // println!("FSM: {:?}", fsm.clone());
        drop_expression(*fsm);
        logger.log("Dropping Expression", 1);
        drop(transitions);
        logger.log(&*format!("Finished model {}", symbol_map.model -1), 1);
        //println!("Symbol map is: {:?}", symbol_map);

    }
    //println!("Symbol map is: {:?}", symbol_map);
    logger.log("Creating gates for all models", 2);
    logger.log(&format!("max_gate_number after unrolling models is: {}", max_gate_number), 1);

    
    let final_string = crate::helper_functions::get_output_string(&model_map, max_gate_number, logger, formula, quantifiers, semantics, layers, &mut symbol_map);
    let mut file = crate::helper_functions::create_file();
    file.write_all(final_string.as_bytes()).expect("Should have been able to write to file");

}


/// Function will unwrap the expression. It should unwrap layers times.
/// We use the fact that the output is the same in every layer, simply different literal gates
/// # Arguments
/// * `expression`: The expression to unwrap
/// * `file`: The file to write the output to
/// * `layers`: The number of times to unwrap the expression
/// * `debug`: Whether to print the fsm
pub fn unwrap(  expression: Vec<Box<Expression>>, 
                formula: &str, 
                layers: i32, 
                logger: &Logger,
                quantifiers: &Vec<(String,String)>, 
                semantics: &String) 
{
    let mut symbol_map = SymbolMap::new(quantifiers.len() as i32, layers);
    // add the models from quantifiers to the symbol map
    symbol_map.setup_model_map(quantifiers);

    let mut model_map: Vec<(String, i32)> = Vec::new();
    // let mut output_str;
    let max_gate_number = 0;
    // let mut conjunction_list: Vec<i32>;
    for expr in expression {
        let fsm = expr.clone();

        // output is (output_string, max_gate_number, symbol_map) for that model
        let (output_str, max_gate_number, _conjunction_list) = create_gates_from_cdf(&fsm, logger, max_gate_number, layers, &mut symbol_map);
        symbol_map.model += 1;
        model_map.push((output_str, max_gate_number));
    }
    logger.log("Creating gates for all models", 2);
    logger.log(&format!("max_gate_number after unrolling models is: {}", max_gate_number), 1);


    let final_string = crate::helper_functions::get_output_string(&model_map, max_gate_number, logger, formula, quantifiers, semantics, layers, &mut symbol_map);
    let mut file = crate::helper_functions::create_file();
    file.write_all(final_string.as_bytes()).expect("Should have been able to write to file");

    logger.log(&*format!("The final string is: {}", final_string), 1);
}



/// Unrolling for the new encoding
/// # Arguments
/// * `expression`: The pairs of initial states and expressions
/// * `layers`: The number of times to unwrap the expression
/// * `debug`: Whether to print the fsm
/// * `quantifiers`: The quantifiers for the model
/// * `semantics`: The semantics for the model
/// * `logger`: The logger
/// * `formula`: The formula for the models
/// * `flags`: The flags for the program
pub fn encoding_unroll(     expression: Vec<(String, String)>, 
                            formula: &str, 
                            layers: i32, 
                            logger: &Logger, 
                            quantifiers: &Vec<(String, String)>, 
                            semantics: &String,
                            model_flag: &String) 
{
    // Used variables
    // println!("Encoding unroll");
    let mut symbol_map = SymbolMap::new(expression.len() as i32, layers);
    symbol_map.setup_model_map(quantifiers);
    let mut model_map: Vec<(String, i32)> = Vec::new();
    // let mut output_str = String::new();
    let mut max_gate_number = 0;
    // let mut c_list: Vec<i32>;

    // This is the model to apply encoding to if we specified it
    let mut model_mum = -1;
    if !model_flag.is_empty(){
        // println!("Length of model_flag {}", model_flag.len());
        model_mum = symbol_map.get_model_number_from_name(model_flag).clone();
    }


    // for every input file with its pair initial states file
    for (initial, express) in expression {
        if model_flag.is_empty() | (model_mum == symbol_map.model) {
            symbol_map.add_initials(&initial);
            logger.log("Starting input to expression", 1);
            let fsm = input_to_expression_optimized(&express, &layers, &mut symbol_map, &mut max_gate_number);

            // Note that the max_gate_number here is the T(v,v') gate number to be used in encoding
            let (mut output_str, mut max_gate_number, c_list) = create_gates_from_cdf(&fsm, logger, max_gate_number, 1, &mut symbol_map);
            let transition_gate = c_list[0];
            let mut encoder = crate::encoder::Encoder::new(layers, 1, &mut symbol_map);
            encoder.build_association();
            encoder.build_association_gates(logger, &mut max_gate_number, &mut output_str, &transition_gate);

            symbol_map.model += 1;
            model_map.push((output_str, max_gate_number));

            // now drop fsm to save memory
            logger.log("Starting mem drop:", 1);
            logger.log("Dropping fsm", 1);
            drop_expression(*fsm);
            logger.log("Dropping Expression", 1);
            drop(express);
            logger.log(&*format!("Finished model {}", symbol_map.model - 1), 1);
        } else {
            symbol_map.add_initials(&initial);
            logger.log("Starting input to expression", 1);
            let fsm = input_to_expression(&express);
            // output is (output_string, max_gate_number, symbol_map) for that model
            logger.log("Starting create gates from cdf", 1);
            let (output_str, max_gate_number, _) = create_gates_from_cdf(&fsm, logger, max_gate_number, layers, &mut symbol_map);
            symbol_map.model += 1;
            model_map.push((output_str, max_gate_number));

            // now drop fsm to save memory
            logger.log("Starting mem drop:", 1);
            logger.log("Dropping fsm", 1);
            drop_expression(*fsm);
            logger.log("Dropping Expression", 1);
            drop(express);
            logger.log(&*format!("Finished model {}", symbol_map.model - 1), 1);
        }
    }
    logger.log("Creating gates for all models", 2);
    logger.log(&format!("max_gate_number after unrolling models is: {}", max_gate_number), 1);

    // build the final gates of the model and format start of model
    // println!("entering get_output_string_unified");
    let final_string = crate::helper_functions::get_output_string_unified(&model_map, max_gate_number, logger, formula, quantifiers, semantics, layers, &mut symbol_map, true, model_flag);
    let mut file = crate::helper_functions::create_file();
    file.write_all(final_string.as_bytes()).expect("Should have been able to write to file");
    logger.log("Writing to file", 2);
}