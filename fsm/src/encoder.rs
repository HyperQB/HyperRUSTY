use std::collections::HashMap;
use std::fmt::Write as FmtWrite;
use crate::symbol_map::SymbolMap;
use logging::{Logger};
use crate::parser::split_on_value;

#[derive(Debug)]
/// This is the encoder for Tzu-Han's encoding.
/// It is built during the input to expression phase and we can use its association to build the gates
/// The idea is to use locality to speed things up and bypass variable checking. Each layer and model
/// simply increment variable by one, so this gives an easy way to build the gates.
///
/// # Fields
/// * `layers` - The number of layers
/// * `models` - The number of models
/// * `association` - model -> vec[(helper gate, normal gate, name))]
/// * `index` - The current index in the association vector
pub struct Encoder<'a> {
    layers: i32,
    // models: i32,
    association: HashMap<i32,Vec<(i32, i32, String)>>,
    // index: i32,
    symbol_map: &'a mut SymbolMap

}

impl Encoder<'_> {
    /// Creates a new encoder
    ///
    /// # Arguments
    /// * `layers` - The number of layers
    /// * `models` - The number of models
    pub fn new(layers: i32, _models: i32, symbol_map: &mut SymbolMap) -> Encoder {
        Encoder {
            layers,
            // models,
            association: HashMap::new(),
            // index: 0,
            symbol_map
        }
    }

    /// Builds the association vector for current model
    pub fn build_association(&mut self) {
            let model = self.symbol_map.model;
            let mut association_vec: Vec<(i32, i32, String)> = Vec::new();
            let helpers = self.symbol_map.helper_variables.get(&model).unwrap();
            for helper in helpers{
                let (name, layer) = split_on_value(helper, '_');
                if layer != "0" {
                    continue
                }
                let literal = split_on_value(&*name, '_').0;
                let real_gate = self.symbol_map.get_symbol_map(&model).get(&(literal.clone()+"_0")).unwrap();
                let helper_gate = self.symbol_map.get_symbol_map(&model).get(helper).unwrap();
                association_vec.push((*helper_gate, *real_gate, literal));
            }
            self.association.insert(model, association_vec);

        return
    }

    /// prints the association vector
    // pub fn print_association(&self) {
    //     for (model, vec) in &self.association {
    //         // println!("Model: {}", model);
    //         for (helper, real, name) in vec {
    //             // println!("Helper: {}, Real: {}, Name: {}", helper, real, name);
    //         }
    //     }
    // }

    /// builds the association gates
    pub fn build_association_gates(&self, logger: &Logger, max_gate_number: &mut i32, output: &mut String, t_gate: &i32) {
        /*
        We have T(v,v') so now build the rest of the model
        ((x_pre <-> x[0]) /\ (x_post <-> x[1])) \/
        ((y_pre <-> y[0]) /\ (y_post <-> y[1])) \/

        ((x_pre <-> x[1]) /\ (x_post <-> x[2])) \/
        ((y_pre <-> y[1]) /\ (y_post <-> y[2])) \/

        ((x_pre <-> x[2]) /\ (x_post <-> x[3])) \/
        ((y_pre <-> y[2]) /\ (y_post <-> y[3])) -> T(v, v')

        all of these are in association vector
         */
        write!(output, "# association gates for model {}\n", self.symbol_map.model);
        let association = self.association.get(&self.symbol_map.model).unwrap();
        let mut and_gates = Vec::new();
        let mut variable_gates = Vec::new();
        if !logger.get_mode(){
            for layer in 0..self.layers { // each layer does one step of ALL literals in association
                // not that iff and iff becomes (not x_pre or x[0]) and (not x[0] or x_pre) and (not x_post or x[1]) and (not x[1] or x_post)
                // so 4 or as well as 1 and gate per literal

                for literal in association{ // literal is (helper, real, name)
                    let (helper, real, _) = literal;
                    // the four or gates

                    write!(output, "{} = or({},{})\n", *max_gate_number+1, -helper, real+layer).unwrap();
                    write!(output, "{} = or({},{})\n", *max_gate_number+2, helper, -(real+layer)).unwrap();
                    write!(output, "{} = or({},{})\n", *max_gate_number+3, -(helper+1), real+layer+1).unwrap();
                    write!(output, "{} = or({},{})\n", *max_gate_number+4, helper+1, -(real+layer+1)).unwrap();
                    // the and gate
                    write!(output, "{} = and({},{},{},{})\n", *max_gate_number+5, *max_gate_number+1, *max_gate_number+2, *max_gate_number+3,*max_gate_number+4).unwrap();
                    *max_gate_number += 5;
                    and_gates.push(*max_gate_number);
                }
                write!(output, "{} = and({})\n", *max_gate_number+1, and_gates.iter().map(|gate| gate.to_string()).collect::<Vec<String>>().join(",")).unwrap();
                and_gates.clear();
                *max_gate_number += 1;
                variable_gates.push(*max_gate_number);
            }
            // now we do a single or of all the and gates
            write!(output, "{} = or({})\n", *max_gate_number+1, variable_gates.iter().map(|gate| gate.to_string()).collect::<Vec<String>>().join(",")).unwrap();
            *max_gate_number += 1;
            // now we do the implication
            write!(output, "{} = or({},{})\n", *max_gate_number+1, -*max_gate_number, t_gate).unwrap();
            *max_gate_number += 1;
            write!(output, "# Ending association gates for model {}\n", self.symbol_map.model);
        } else{
            for layer in 0..self.layers { // each layer does one step of ALL literals in association
                // not that iff and iff becomes (not x_pre or x[0]) and (not x[0] or x_pre) and (not x_post or x[1]) and (not x[1] or x_post)
                // so 4 or as well as 1 and gate per literal

                for literal in association{ // literal is (helper, real, name)
                    let (_, _, name) = literal;
                    // the four or gates
                    let helper_name = format!("{}_helper", name);

                    write!(output, "g{} = or({},{})\n", *max_gate_number+1, format!("-{}[0]",helper_name), format!("{}[{}]",name,layer)).unwrap();
                    write!(output, "g{} = or({},{})\n", *max_gate_number+2, format!("{}[0]",helper_name), format!("-{}[{}]",name,layer)).unwrap();
                    write!(output, "g{} = or({},{})\n", *max_gate_number+3, format!("-{}[1]",helper_name), format!("{}[{}]",name,layer+1)).unwrap();
                    write!(output, "g{} = or({},{})\n", *max_gate_number+4, format!("{}[1]",helper_name), format!("-{}[{}]",name,layer+1)).unwrap();
                    // the and gate
                    write!(output, "g{} = and(g{},g{},g{},g{})\n", *max_gate_number+5, *max_gate_number+1, *max_gate_number+2, *max_gate_number+3,*max_gate_number+4).unwrap();
                    *max_gate_number += 5;
                    and_gates.push(*max_gate_number);
                }
                write!(output, "g{} = and({})\n", *max_gate_number+1, and_gates.iter().map(|gate| format!("g{}", gate)).collect::<Vec<String>>().join(",")).unwrap();
                and_gates.clear();
                *max_gate_number += 1;
                variable_gates.push(*max_gate_number);
            }
            // now we do a single or of all the and gates
            write!(output, "g{} = or({})\n", *max_gate_number+1, variable_gates.iter().map(|gate| format!("g{}", gate)).collect::<Vec<String>>().join(",")).unwrap();
            *max_gate_number += 1;
            // now we do the implication
            write!(output, "g{} = or({},g{})\n", *max_gate_number+1, format!("-g{}",*max_gate_number), t_gate).unwrap();
            *max_gate_number += 1;
            write!(output, "# Ending association gates for model {}\n", self.symbol_map.model);
        }


    }
}