use std::collections::{HashMap, VecDeque};
use expressions::{Expression, Literal};
use logging::raise_error;
use crate::input_to_expressions::input_to_expression;
use indexmap::IndexSet;

/// This struct is used to map symbols to gate numbers
/// It is used to keep track of the gate numbers for each symbol in each model and layer
///
/// # Fields
/// * `symbol_map` - A hashmap that maps model numbers to a hashmap that maps symbols to gate numbers
/// * `model_map` - A hashmap that maps model names to model numbers
/// * `initial_map` - A hashmap that maps model numbers to the initial state
/// * `models` - The number of models
/// * `layers` - The number of layers
/// * `model` - The current model
/// * `helper_variables` - A hashmap that maps model numbers to a vector of tuples that maps the gate number to the symbol
#[derive(Debug)]
pub struct SymbolMap {
    symbol_map: HashMap<i32, HashMap<String,i32>>, // model -> (symbol -> gate)
    model_map: HashMap<String,i32>, // Model number to model name
    _initial_map: HashMap<i32, String>, // Model-> to initial state
    _expression_map: HashMap<(i32,i32), HashMap<Expression,i32>>, // (layer, model) -> (expression -> gate)
    _models: i32,
    layers: i32,
    pub(crate) model: i32,
    pub(crate) helper_variables: HashMap<i32,IndexSet<String>> // model -> (gate, symbol) only the helper ones
}

impl SymbolMap {
    pub fn new(_models: i32, layers: i32) -> SymbolMap {
        SymbolMap {
            symbol_map: HashMap::new(),
            model_map: HashMap::new(),
            _models,
            _expression_map: HashMap::new(),
            layers,
            model: 0,
            _initial_map: HashMap::new(),
            helper_variables: HashMap::new()
        }
    }

    /// Inserts symbols into the symbol map for each model and layer all at once. This minimizes
    /// The how large the number of each constant gate can get
    ///
    /// # Arguments
    /// * `symbol` - The symbol to insert
    /// * `gate` - The current gate number
    pub fn insert(&mut self, symbol: String, gate: &mut i32){
        // Add the var to each model and layer
        let model = self.model;
            for layer in 0..self.layers+1 {
                *gate += 1;
                self.symbol_map.entry(model).or_insert(HashMap::new()).insert(symbol.clone()+"_"+&*layer.to_string(), *gate);
            }

    }

    /// Inserts a HELPER symbol into the symbol map for each model and for normal and prime variables
    /// This is used with Tzu-Han's encoding. In that encoding, the insert function inserts the
    /// real variables. This is used to insert the helper variables themselves
    ///
    /// # Arguments
    /// * `symbol` - The symbol to insert
    /// * `gate` - The current gate number
    pub fn insert_helper(&mut self, symbol: String, gate: &mut i32){
        // Add the var to each model and layer
        let model = self.model;
            for layer in 0..2 {
                *gate += 1;
                self.symbol_map.entry(model).or_insert(HashMap::new()).insert(symbol.clone()+"_helper_"+&*layer.to_string(), *gate);
                self.helper_variables.entry(model).or_insert(IndexSet::new()).insert(symbol.clone()+"_helper_"+&*layer.to_string());

            }
    }

    /// Gets the gate number for a symbol
    ///
    /// # Arguments
    /// * `symbol` - The symbol to get the gate number for
    ///
    /// # Returns
    /// * The gate number for the symbol
    /// * None if the symbol is not found
    pub fn get(&self, symbol: &String) -> Option<&i32> {
        let model = self.symbol_map.get(&self.model);
        if model.is_none() {
            return None;
        }
        let model = model.unwrap();
        return model.get(symbol);
    }

    /// Gets the symbol map for a model.
    ///
    /// # Arguments
    /// * `model` - The model to get the symbol map for
    ///
    /// # Returns
    /// * The symbol map for the model
    pub fn get_symbol_map(&self, model: &i32) -> &HashMap<String,i32> {
        let temp = self.symbol_map.get(model);
        if temp.is_none() {
            raise_error(&*format!("Model {} does not exist. Please check your hq to see if the model exists", model), 5);
        }
        let model = temp.unwrap();
        return model;
    }

    /// Sets up the model map based on the quantifier input
    pub fn setup_model_map(&mut self, quantifiers: &Vec<(String,String)>){
        for (_,model) in quantifiers {
            self.model_map.insert(model.clone(), self.model);
            self.model += 1;
        }
        self.model = 0;
    }

    /// function to get the model name from the model number
    ///
    /// # Arguments
    /// * `model` - The model number
    pub fn get_model_number_from_name(&self, model: &String) -> &i32 {
        let temp = self.model_map.get(model);
        if temp.is_none() {
            raise_error(&*format!("Model {} does not exist. Please check your hq to see if the model exists", model), 5);
        }
        let model = temp.unwrap();
        return model;
    }

    pub fn add_initials(&mut self, initial: &String){
        self._initial_map.insert(self.model, initial.clone());
    }

    pub fn get_initials(& self, model: &i32) -> Vec<String> {
        let temp = self._initial_map.get(model);
        if temp.is_none() {
            return vec![];
        }
        let initial_string = temp.unwrap();
        // println!("Initials are");

        // println!("{:?}", input_to_expression(initial_string));
        self.parse_initial_states(initial_string)
    }

    pub fn get_initial_expression(& self, model:&i32) -> Box<Expression> {
        let temp = self._initial_map.get(model);
        if temp.is_none() {
            return Box::from(Expression::Literal(Literal::Atom("".to_owned())));
        }
        let initial_string = temp.unwrap();
        input_to_expression(initial_string)
    }

    /// This function parses the initial states and returns a vector of the initial states and if they
    /// are negated or not
    ///
    /// # Arguments
    /// * `initial` - The initial state string
    fn parse_initial_states(&self, initial: &String) -> Vec<String> {
        let initial_expression = input_to_expression(initial); // a bunch of MAnds and nots
        let mut stack: VecDeque<(&Expression, bool)> = VecDeque::new();
        let mut initial_states: Vec<String> = Vec::new();
        stack.push_back((&initial_expression, false));
        while let Some(curr_node) = stack.pop_front(){
            let expression = curr_node.0;
            let negation = curr_node.1;
            match expression {
                Expression::And(ref left, ref right) => {
                    stack.push_back((left, negation));
                    stack.push_back((right, negation));
                }
                Expression::MAnd(ref inner) => {
                    for i in inner {
                        stack.push_back((i, negation));
                    }
                },
                Expression::Neg(inner) => {
                    stack.push_back((inner, !negation));
                }
                Expression::Literal(inner) => {
                    if !negation {
                        if let Literal::Atom(symbol) = inner {
                            initial_states.push(symbol.clone());
                        }
                    }
                }
                _ => {
                    // raise_error("Initial state must be a conjunction of variables and negations", 5);
                }
            }
        }
        return initial_states;
    }

    pub fn print(&self){
        // println!("{:?}", self.symbol_map);
    }
}



#[cfg(test)]
mod tests {
    use super::*;

    fn init_symbol_map() -> SymbolMap {
        SymbolMap::new(2, 2)
    }

    #[test]
    fn test_parse_initial_states() {
        let mut symbol_map = init_symbol_map();
        let initial = r"~(c/\b)/\a".to_owned();
        symbol_map.add_initials(&initial);
        let initial_states = symbol_map.parse_initial_states(&initial);
        assert_eq!(initial_states, vec!["a"]);

        let initial = r"(c/\b)/\a/\~d".to_owned();
        symbol_map.add_initials(&initial);
        let mut initial_states = symbol_map.parse_initial_states(&initial);
        assert_eq!(initial_states.sort(), vec!["a", "b", "c"].sort());

        let initial = r"(a/\b)/\(c/\~(d/\~e))".to_owned(); // a,b,c,e
        symbol_map.add_initials(&initial);
        initial_states = symbol_map.parse_initial_states(&initial);
        assert_eq!(initial_states.sort(), vec!["a", "b", "c", "e"].sort());
    }
}