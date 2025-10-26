// use std::collections::HashMap;
use indexmap::IndexMap;
use z3::{
    ast::{
        Ast, Bool, Dynamic, 
        Int, BV,
    },
    Context,
};
use std::collections::{HashMap, VecDeque};


#[macro_use]
pub mod macros;

#[derive(Debug, Clone)]
pub enum VarType {
    Bool {
        init: Option<Vec<bool>>,
    },
    Int {
        init: Option<Vec<i64>>,
        lower: Option<i64>,
        upper: Option<i64>,
    },
    BVector {
        width: u32,
        lower: Option<i64>,
        upper: Option<i64>,
        init:  Option<Vec<i64>>,
    },
}

#[derive(Debug, Clone)]
pub enum ReturnType<'ctx> {
    Bool(Vec<bool>),
    Int(Vec<i64>),
    BVector(Vec<(i64, u32)>), // (element, size)
    DynAst(Dynamic<'ctx>),
}

/// Concrete value for one variable
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ConcreteVal {
    B(bool),
    I(i64),
    BV(i64, u32),
}

pub type ConcreteState<'ctx> = IndexMap<&'ctx str, ConcreteVal>;

pub struct BFSExplicit<'ctx> {
    pub states: Vec<ConcreteState<'ctx>>, // index -> concrete state
    pub edges:  Vec<(usize, usize)>,      // (u -> v)
    pub adjacency: Vec<Vec<bool>>,        // adjacency[u][v] == true
}

#[derive(Debug, Clone)]
pub struct Variable {
    pub sort: VarType,
}

pub type EnvState<'ctx> = IndexMap<&'ctx str, Dynamic<'ctx>>;

// #[derive(Debug, Clone)]
pub struct SMVEnv<'ctx> {
    pub ctx: &'ctx Context,
    // The Variable type already has the name. Do we require the name there?
    pub variables: IndexMap<&'ctx str, Variable>,
    pub predicates: IndexMap<&'ctx str, Box<dyn Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> Bool<'ctx>>>,
    pub transitions: IndexMap<&'ctx str, Vec<(Box<dyn Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> ReturnType<'ctx>>, Box<dyn Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> ReturnType<'ctx>>)>>,
}

// Milad: I need this (???)
impl<'ctx> ReturnType<'ctx> {
    pub fn into_dynamic(self, ctx: &'ctx z3::Context, _env: &SMVEnv<'ctx>, state: &EnvState<'ctx>, var_name: &str) -> Dynamic<'ctx> {
        match self {
            ReturnType::Int(vals) => {
                let sym = int_var!(state, var_name);
                let disjuncts: Vec<_> = vals.iter()
                    .map(|val| sym._eq(&z3::ast::Int::from_i64(ctx, *val)))
                    .collect();
                z3::ast::Bool::or(ctx, &disjuncts.iter().collect::<Vec<_>>()).into()
            }
            ReturnType::Bool(vals) => {
                let sym = bool_var!(state, var_name);
                let disjuncts: Vec<_> = vals.iter()
                    .map(|val| sym._eq(&z3::ast::Bool::from_bool(ctx, *val)))
                    .collect();
                z3::ast::Bool::or(ctx, &disjuncts.iter().collect::<Vec<_>>()).into()
            }
            ReturnType::BVector(_) => {
                panic!("into_dynamic not implemented for BVector")
            }
            ReturnType::DynAst(ast) => ast,
        }
    }
}

impl<'ctx> SMVEnv<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        SMVEnv {
            ctx: ctx,
            variables: IndexMap::new(),
            predicates: IndexMap::new(),
            transitions: IndexMap::new(),
        }
    }

    pub fn register_variable(&mut self, name: &'ctx str, sort: VarType) {
        let new_variable = Variable {
            sort,
        };

        self.variables.insert(name, new_variable);
    }

    pub fn register_predicate(&mut self, name: &'ctx str, f: impl Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> Bool<'ctx> + 'static) {
        self.predicates.insert(name, Box::new(f));
    }

    pub fn register_transition(&mut self, name: &'ctx str, condition: impl Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> ReturnType<'ctx> + 'static, update: impl Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> ReturnType<'ctx> + 'static) {
        // If variable name does not exist, panic!
        let _panic_only = self.variables.get(name).expect("undefined variable name {name}");

        // If we haven't registered any transition for this variable,
        // the name must be registered first.
        let name_entry = self.transitions.entry(name).or_insert_with(Vec::new);

        // register the transition
        name_entry.push((Box::new(condition), Box::new(update)));
    }

    fn generate_state_variables(& self, bound: usize, suffix: Option<&'ctx str>) -> Vec<EnvState<'ctx>> {
        let mut states = Vec::new();

        // let suffix = name.unwrap_or("");
        
        for k in 0..=bound {
            let mut curr = EnvState::<'ctx>::new();

            for (name, variable) in self.variables.iter() {
                let state_name = match suffix {
                    Some(path_name) => format!("{}_{}_{}", name, k, path_name),
                    None => format!("{}_{}", name, k),
                };
                let node : Dynamic<'ctx> = match variable.sort {
                    VarType::Bool {init: _} => {
                        Dynamic::from_ast(&Bool::new_const(self.ctx, state_name))
                    }
                    VarType::Int{init: _, lower: _, upper: _} => {
                        Dynamic::from_ast(&Int::new_const(self.ctx, state_name))
                    }
                    VarType::BVector{width, lower: _, upper: _, init: _} => {
                        Dynamic::from_ast(&BV::new_const(self.ctx, state_name, width))

                    }
                };
                curr.insert(name, node);
            }

            states.push(curr);
        }
        states
    }

    fn generate_bound_constraints(& self, states: &Vec<EnvState<'ctx>>) -> Vec<Bool> {
        let mut constraints = Vec::<Bool>::new();

        // Iterate through each variable and generate the bound condition
        //  for every state
        for (name, variable) in self.variables.iter() {
            let constraint = match &variable.sort {
                VarType::Int {lower, upper, ..} => {
                    let mut bound_constraints = Vec::new();
                    for state in states {
                        let var = int_var!(state, name);
                        match lower {
                            Some(v) => {
                                bound_constraints.push(var.ge(&Int::from_i64(self.ctx, *v)));
                            }
                            None => ()
                        };
                        match upper {
                            Some(v) => {
                                bound_constraints.push(var.le(&Int::from_i64(self.ctx, *v)));
                            }
                            None => ()
                        };
                    }
                    // Conjunct all bound constraints
                    let refs: Vec<&Bool> = bound_constraints.iter().collect();
                    Some(Bool::and(self.ctx, &refs))
                }
                VarType::BVector {lower, upper, width, ..} => {
                    let mut bound_constraints = Vec::new();
                    for state in states {
                        let var = bv_var!(state, name);
                        match lower {
                            Some(v) => {
                                bound_constraints.push(var.bvuge(&BV::from_i64(self.ctx, *v, *width)));
                            }
                            None => ()
                        };
                        match upper {
                            Some(v) => {
                                bound_constraints.push(var.bvule(&BV::from_i64(self.ctx, *v, *width)));
                            }
                            None => ()
                        };
                    }
                    // Conjunct all bound constraints
                    let refs: Vec<&Bool> = bound_constraints.iter().collect();
                    Some(Bool::and(self.ctx, &refs))
                }
                // Other types need not to have a bound
                _ => None
            };
            match constraint {
                Some(c) => constraints.push(c),
                _ => ()
            };
        }
        constraints
    }

    pub fn generate_initial_constraints(& self, states: &Vec<EnvState<'ctx>>) -> Vec<Bool> {
        let mut constraints = Vec::<Bool>::new();

        for (name, variable) in self.variables.iter() {
            let constraint = match &variable.sort {
                VarType::Bool {init} => {
                    // Handle Initial values
                    let constraint = if let Some(values) = init {
                        
                        // Get initial state's variable for this name
                        let var = states[0].get(name).unwrap(); // It definitely exists
                        // Given the Bool as the type, we can cast it to a Boolean
                        let var = var.as_bool().unwrap(); // It is definitely a Boolean
                        
                        // If the length of the 'value' is 1, set the constraint manually
                        if values.len() > 1 {
                            let mut comparisons = Vec::new();
                            for val in values {
                                let ast_val = Bool::from_bool(self.ctx, *val);
                                comparisons.push(var._eq(&ast_val));
                            }
                            // Build a disjunction
                            let refs: Vec<&Bool> = comparisons.iter().collect();
                            Some(Bool::or(self.ctx, &refs))
                        }else {
                            let ast_val = Bool::from_bool(self.ctx, values[0]);
                            Some(var._eq(&ast_val))
                        }
                    }else {
                        None
                    };
                    constraint
                }
                VarType::Int{init, lower: _, upper: _} => {
                    let constraint = if let Some(values) = init {
                        
                        // Get initial state's variable for this name
                        let var = states[0].get(name).unwrap(); // It definitely exists
                        // Given the Int as the type, we can cast it to an Integer
                        let var = var.as_int().unwrap(); // It is definitely an Integer
                        
                        // If the length of the 'value' is 1, set the constraint manually
                        if values.len() > 1 {
                            let mut comparisons = Vec::new();
                            for val in values {
                                let ast_val = Int::from_i64(self.ctx, *val);
                                comparisons.push(var._eq(&ast_val));
                            }
                            // Build a disjunction
                            let refs: Vec<&Bool> = comparisons.iter().collect();
                            Some(Bool::or(self.ctx, &refs))
                        }else {
                            let ast_val = Int::from_i64(self.ctx, values[0]);
                            Some(var._eq(&ast_val))
                        }
                    }else {
                        None
                    };
                    constraint
                }
                VarType::BVector{width, lower: _, upper: _, init} => {
                    let constraint = if let Some(values) = init {
                        
                        // Get initial state's variable for this name
                        let var = states[0].get(name).unwrap(); // It definitely exists
                        // Given the BV as the type, we can cast it to a BV
                        let var = var.as_bv().unwrap(); // It is definitely a BV
                        
                        // If the length of the 'value' is 1, set the constraint manually
                        if values.len() > 1 {
                            let mut comparisons = Vec::new();
                            for val in values {
                                let ast_val = BV::from_i64(self.ctx, *val, *width);
                                comparisons.push(var._eq(&ast_val));
                            }
                            // Build a disjunction
                            let refs: Vec<&Bool> = comparisons.iter().collect();
                            Some(Bool::or(self.ctx, &refs))
                        }else {
                            let ast_val = BV::from_i64(self.ctx, values[0], *width);
                            Some(var._eq(&ast_val))
                        }
                    }else {
                        None
                    };
                    constraint
                }
            };

            match constraint {
                Some(b) => constraints.push(b),
                None => (),
            };
        }
        constraints
    }

    // SHIT CODE, but we didnt want ro resolve dependencies (I WAS FORCED HERE)
    pub fn generate_initial_constraints_for_state(& self, states: &Vec<EnvState<'ctx>>, i: usize) -> Vec<Bool> {
        let mut constraints = Vec::<Bool>::new();

        for (name, variable) in self.variables.iter() {
            let constraint = match &variable.sort {
                VarType::Bool {init} => {
                    // Handle Initial values
                    let constraint = if let Some(values) = init {
                        
                        // Get initial state's variable for this name
                        let var = states[i].get(name).unwrap(); // It definitely exists
                        // Given the Bool as the type, we can cast it to a Boolean
                        let var = var.as_bool().unwrap(); // It is definitely a Boolean
                        
                        // If the length of the 'value' is 1, set the constraint manually
                        if values.len() > 1 {
                            let mut comparisons = Vec::new();
                            for val in values {
                                let ast_val = Bool::from_bool(self.ctx, *val);
                                comparisons.push(var._eq(&ast_val));
                            }
                            // Build a disjunction
                            let refs: Vec<&Bool> = comparisons.iter().collect();
                            Some(Bool::or(self.ctx, &refs))
                        }else {
                            let ast_val = Bool::from_bool(self.ctx, values[0]);
                            Some(var._eq(&ast_val))
                        }
                    }else {
                        None
                    };
                    constraint
                }
                VarType::Int{init, lower: _, upper: _} => {
                    let constraint = if let Some(values) = init {
                        
                        // Get initial state's variable for this name
                        let var = states[i].get(name).unwrap(); // It definitely exists
                        // Given the Int as the type, we can cast it to an Integer
                        let var = var.as_int().unwrap(); // It is definitely an Integer
                        
                        // If the length of the 'value' is 1, set the constraint manually
                        if values.len() > 1 {
                            let mut comparisons = Vec::new();
                            for val in values {
                                let ast_val = Int::from_i64(self.ctx, *val);
                                comparisons.push(var._eq(&ast_val));
                            }
                            // Build a disjunction
                            let refs: Vec<&Bool> = comparisons.iter().collect();
                            Some(Bool::or(self.ctx, &refs))
                        }else {
                            let ast_val = Int::from_i64(self.ctx, values[0]);
                            Some(var._eq(&ast_val))
                        }
                    }else {
                        None
                    };
                    constraint
                }
                VarType::BVector{width, lower: _, upper: _, init} => {
                    let constraint = if let Some(values) = init {
                        
                        // Get initial state's variable for this name
                        let var = states[i].get(name).unwrap(); // It definitely exists
                        // Given the BV as the type, we can cast it to a BV
                        let var = var.as_bv().unwrap(); // It is definitely a BV
                        
                        // If the length of the 'value' is 1, set the constraint manually
                        if values.len() > 1 {
                            let mut comparisons = Vec::new();
                            for val in values {
                                let ast_val = BV::from_i64(self.ctx, *val, *width);
                                comparisons.push(var._eq(&ast_val));
                            }
                            // Build a disjunction
                            let refs: Vec<&Bool> = comparisons.iter().collect();
                            Some(Bool::or(self.ctx, &refs))
                        }else {
                            let ast_val = BV::from_i64(self.ctx, values[0], *width);
                            Some(var._eq(&ast_val))
                        }
                    }else {
                        None
                    };
                    constraint
                }
            };

            match constraint {
                Some(b) => constraints.push(b),
                None => (),
            };
        }
        constraints
    }

    

    
    pub fn generate_transition_relation(
    &self,
    curr_state: &EnvState<'ctx>,
    next_state: &EnvState<'ctx>,
) -> Vec<Bool<'ctx>> {
    use z3::ast::{Bool, Int, BV};

    let mut constraints: Vec<Bool> = Vec::new();
    // let mut change_flags: Vec<Bool> = Vec::new(); // track (next != curr) per variable

        for (name, variable) in self.variables.iter() {
            // If transitions have been defined for this variable, build a nested if-expression.
            match self.transitions.get(name) {
                Some(_transitions) => {
                    // Start with the implicit TRUE case which carries the value forward
                    let mut expr = match &variable.sort {
                        VarType::Bool {..} => {
                            let curr_var = bool_var!(curr_state, name);
                            let next_var = bool_var!(next_state, name);
                            next_var._eq(&curr_var)
                        }
                        VarType::Int {..} => {
                            let curr_var = int_var!(curr_state, name);
                            let next_var = int_var!(next_state, name);
                            next_var._eq(&curr_var)
                        }
                        VarType::BVector {..} => {
                            let curr_var = bv_var!(curr_state, name);
                            let next_var = bv_var!(next_state, name);
                            next_var._eq(&curr_var)
                        }
                    };

                    let transitions_for_name = self.transitions.get(name).unwrap();

                    for (cond, update) in transitions_for_name.into_iter().rev() {
                        // Handle Non-deterministic updates
                        // A non-deterministic block is just a disjunction block
                        let update_body = match update(self, self.ctx, curr_state) {
                            ReturnType::Bool(v) => {
                                let next_var = bool_var!(next_state, name);
                                // Check the length of the vector
                                if v.len() > 1 {
                                    // Non-deterministic transition
                                    let mut next_transitions = Vec::new();
                                    for val in v {
                                        let ast_val = Bool::from_bool(self.ctx, val);
                                        next_transitions.push(next_var._eq(&ast_val));
                                    }
                                    // Build a disjunction
                                    let refs: Vec<&Bool> = next_transitions.iter().collect();
                                    Bool::or(self.ctx, &refs)
                                }else {
                                    // Handle deterministic transition
                                    let ast_val = Bool::from_bool(self.ctx, v[0]);
                                    next_var._eq(&ast_val)
                                }
                            }
                            ReturnType::Int(v) => {
                                let next_var = int_var!(next_state, name);
                                // Check the length of the vector
                                if v.len() > 1 {
                                    // Non-deterministic transition
                                    let mut next_transitions = Vec::new();
                                    for val in v {
                                        let ast_val = Int::from_i64(self.ctx, val);
                                        next_transitions.push(next_var._eq(&ast_val));
                                    }
                                    // Build a disjunction
                                    let refs: Vec<&Bool> = next_transitions.iter().collect();
                                    Bool::or(self.ctx, &refs)
                                }else {
                                    // Handle deterministic transition
                                    let ast_val = Int::from_i64(self.ctx, v[0]);
                                    next_var._eq(&ast_val)
                                }
                            }
                            ReturnType::BVector(v) => {
                                let next_var = bv_var!(next_state, name);
                                // Check the length of the vector
                                if v.len() > 1 {
                                    // Non-deterministic transition
                                    let mut next_transitions = Vec::new();
                                    for val in v {
                                        let ast_val = BV::from_i64(self.ctx, val.0, val.1);
                                        next_transitions.push(next_var._eq(&ast_val));
                                    }
                                    // Build a disjunction
                                    let refs: Vec<&Bool> = next_transitions.iter().collect();
                                    Bool::or(self.ctx, &refs)
                                }else {
                                    // Handle deterministic transition
                                    let ast_val = BV::from_i64(self.ctx, v[0].0, v[0].1);
                                    next_var._eq(&ast_val)
                                }
                            }
                            ReturnType::DynAst(node) => match &variable.sort {
                                VarType::Bool {..} => {
                                    let next_var = bool_var!(next_state, name);
                                    next_var._eq(&node.as_bool().unwrap())
                                }
                                VarType::Int {..} => {
                                    let next_var = int_var!(next_state, name);
                                    next_var._eq(&node.as_int().unwrap())
                                }
                                VarType::BVector {..} => {
                                    let next_var = bv_var!(next_state, name);
                                    next_var._eq(&node.as_bv().unwrap())
                                }
                            }
                        };
                        // cond always returns a bool value or a Dynamic Ast which we turn into a Bool
                        let result = match cond(self, self.ctx, curr_state) {
                            ReturnType::Bool(v) => {
                                Bool::from_bool(self.ctx, v[0])
                            }
                            ReturnType::DynAst(node) => {
                                // It should be a bool node
                                node.as_bool().expect("Expected ast::Bool Node inside `cond`")
                            }
                            _ => panic!("Expected ast::Bool Node inside `cond`")
                        };
                        expr = Bool::ite(&result, &update_body, &expr);
                    }
                    constraints.push(expr);
                }
                // What happens when no transition is defined?
                // We impose no constraint on that variable
                None => (),
            };
        }
        constraints
    }

    pub fn generate_symbolic_path(& self, bound: usize, suffix: Option<&'ctx str>) -> (Vec<EnvState<'ctx>>, Bool) {
        let states = self.generate_state_variables(bound, suffix);
        
        // A list of constraints - Initialized by initial constraints
        let mut constraints = self.generate_initial_constraints(&states);
        // Extend it to include bound constraints
        constraints.extend(self.generate_bound_constraints(&states));

        // Add transition constraints for each step (unrolling process)
        for k in 0..bound {
            let curr_state = &states[k];
            let next_state = &states[k + 1];
            let step_constraint = self.generate_transition_relation(curr_state, next_state);
            constraints.extend(step_constraint);
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        let sym_path = Bool::and(self.ctx, &refs);
        (states, sym_path)
    }

    pub fn get_transitions(&self) -> &IndexMap<&'ctx str, Vec<(Box<dyn Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> ReturnType<'ctx>>, Box<dyn Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> ReturnType<'ctx>>)>> {
        &self.transitions
    }

    pub fn make_dummy_state(&self, ctx: &'ctx z3::Context) -> EnvState<'ctx> {
        let mut state: EnvState<'ctx> = IndexMap::new();
 
        for (name, var) in &self.variables {
            let val = match &var.sort {
                VarType::Bool { .. } => {
                    let ast = z3::ast::Bool::fresh_const(ctx, name);
                    Dynamic::from_ast(&ast)
                }
                VarType::Int { .. } => {
                    let ast = z3::ast::Int::fresh_const(ctx, name);
                    Dynamic::from_ast(&ast)
                }
                VarType::BVector { width, .. } => {
                    let ast = z3::ast::BV::fresh_const(ctx, name, *width);
                    Dynamic::from_ast(&ast)
                }
            };
            state.insert(*name, val);
        }
 
        state
    }

    pub fn make_enum_dummy_state(&self, ctx: &'ctx z3::Context, _idx: usize, _model: usize) -> EnvState<'ctx> {
        let mut state: EnvState<'ctx> = IndexMap::new();
        for (name, var) in &self.variables {
            // let base = format!("{name}_{idx}_{model}");
            let val = match &var.sort {
                VarType::Bool { .. } => {
                    let ast = z3::ast::Bool::fresh_const(ctx, name);
                    Dynamic::from_ast(&ast)
                }
                VarType::Int { .. } => {
                    let ast = z3::ast::Int::fresh_const(ctx, name);
                    Dynamic::from_ast(&ast)
                }
                VarType::BVector { width, .. } => {
                    let ast = z3::ast::BV::fresh_const(ctx, name, *width);
                    Dynamic::from_ast(&ast)
                }
            };
            state.insert(*name, val);
        }

        state
    }
    
 
    pub fn get_context(&self) -> &'ctx z3::Context {
        self.ctx
    }
 
    pub fn get_variables(&self) -> &IndexMap<&'ctx str, Variable> {
        &self.variables
    }
 
    pub fn get_variable_mut(&mut self, name: &str) -> Option<&mut Variable> {
        self.variables.get_mut(name)
    }
 
    pub fn get_variable_type(&self, name: &str) -> Option<&VarType> {
        // println!("Looking up variable type for: {}", name);
        self.variables.get(name).map(|var| &var.sort)
    }

    pub fn generate_all_symbolic_states(&self, suffix: Option<&'ctx str>) -> Vec<EnvState<'ctx>> {
        let mut total_states = 1;

        // Step 1: Compute total number of possible states
        for (_, var) in self.variables.iter() {
            let domain_size = match &var.sort {
                VarType::Bool { .. } => 2,
                VarType::Int { lower, upper, .. } => {
                    match (lower, upper) {
                        (Some(lo), Some(hi)) => (hi - lo + 1).max(0),
                        _ => panic!("Int vars must have both lower and upper bounds for full state space generation."),
                    } 
                }
                VarType::BVector { lower, upper, .. } => {
                    match (lower, upper) {
                        (Some(lo), Some(hi)) => (hi - lo + 1).max(0),
                        _ => panic!("BV vars must have both lower and upper bounds for full state space generation."),
                    }
                }
            };
            total_states *= domain_size;
        }

        // Step 2: Use previous logic to generate symbolic variables
        let mut states = Vec::new();

        for k in 0..total_states {
            let mut state = EnvState::<'ctx>::new();

            for (name, variable) in self.variables.iter() {
                let state_name = match suffix {
                    Some(s) => format!("{}_{}_{}", name, k, s),
                    None => format!("{}_{}", name, k),
                };

                let node = match variable.sort {
                    VarType::Bool {init: _} => {
                        Dynamic::from_ast(&Bool::new_const(self.ctx, state_name))
                    }
                    VarType::Int {init: _, lower: _, upper: _} => {
                        Dynamic::from_ast(&Int::new_const(self.ctx, state_name))
                    }
                    VarType::BVector {width, lower: _, upper: _, init: _} => {
                        Dynamic::from_ast(&BV::new_const(self.ctx, state_name, width))
                    }
                };

                state.insert(name, node);
            }

            states.push(state);
        }

        states
    }


    pub fn generate_scope_constraints_for_state(&self, state: &EnvState<'ctx>) -> Vec<Bool<'ctx>> {
        let mut constraints = Vec::<Bool<'ctx>>::new();

        // Iterate through each variable and generate its bound condition for this one state
        for (name, variable) in self.variables.iter() {
            let constraint = match &variable.sort {
                VarType::Bool { .. } => None,
                VarType::Int { lower, upper, .. } => {
                    let mut per_var = Vec::new();
                    let v = int_var!(state, name);
                    if let Some(lo) = lower {
                        per_var.push(v.ge(&Int::from_i64(self.ctx, *lo)));
                    }
                    if let Some(hi) = upper {
                        per_var.push(v.le(&Int::from_i64(self.ctx, *hi)));
                    }
                    // Conjunct all per‐variable constraints (if any)
                    let refs: Vec<&Bool<'ctx>> = per_var.iter().collect();
                    Some(Bool::and(self.ctx, &refs))
                }
                VarType::BVector { lower, upper, width, .. } => {
                    let mut per_var = Vec::new();
                    let v = bv_var!(state, name);
                    if let Some(lo) = lower {
                        per_var.push(v.bvsge(&BV::from_i64(self.ctx, *lo, *width)));
                    }
                    if let Some(hi) = upper {
                        per_var.push(v.bvsle(&BV::from_i64(self.ctx, *hi, *width)));
                    }
                    let refs: Vec<&Bool<'ctx>> = per_var.iter().collect();
                    Some(Bool::and(self.ctx, &refs))
                }
            };

            if let Some(c) = constraint {
                constraints.push(c);
            }
        }

        constraints
    }

/// Helper: pin the *current* symbolic vars to a concrete assignment
 fn pin_curr_equalities(
        &self,
        curr_sym: &EnvState<'ctx>,
        curr_vals: &ConcreteState<'ctx>,
    ) -> Vec<Bool<'ctx>> {
        let mut eqs = Vec::new();
        for (name, var) in &self.variables {
            let cv = curr_vals.get(name)
                .unwrap_or_else(|| panic!("missing concrete value for '{}'", name));
            match (var.sort.clone(), cv) {
                (VarType::Bool { .. }, ConcreteVal::B(b)) => {
                    let v = bool_var!(curr_sym, name);
                    eqs.push(v._eq(&Bool::from_bool(self.ctx, *b)));
                }
                (VarType::Int { .. }, ConcreteVal::I(n)) => {
                    let v = int_var!(curr_sym, name);
                    eqs.push(v._eq(&Int::from_i64(self.ctx, *n)));
                }
                (VarType::BVector { width, .. }, ConcreteVal::BV(n, w))
                    if width == *w =>
                {
                    let v = bv_var!(curr_sym, name);
                    eqs.push(v._eq(&BV::from_i64(self.ctx, *n, *w)));
                }
                _ => panic!("type mismatch for variable '{}'", name),
            }
        }
        eqs
    }

    /// Helper: read a concrete state from model for the *next* symbolic vars
    fn model_to_concrete_next(
        &self,
        next_sym: &EnvState<'ctx>,
        m: &z3::Model<'ctx>,
    ) -> ConcreteState<'ctx> {
        let mut out: ConcreteState<'ctx> = IndexMap::new();
        for (name, var) in &self.variables {
            match &var.sort {
                VarType::Bool { .. } => {
                    let v = bool_var!(next_sym, name);
                    let b = m.eval(&v, true).expect("eval").as_bool().expect("bool");
                    out.insert(*name, ConcreteVal::B(b));
                }
                VarType::Int { .. } => {
                    let v = int_var!(next_sym, name);
                    let n = m.eval(&v, true).expect("eval").as_i64().expect("i64");
                    out.insert(*name, ConcreteVal::I(n));
                }
                VarType::BVector { width, .. } => {
                    let v = bv_var!(next_sym, name);
                    let n = m.eval(&v, true).expect("eval").as_i64().expect("i64");
                    out.insert(*name, ConcreteVal::BV(n, *width));
                }
            }
        }
        out
    }

    /// Core primitive:
    /// Given (1) a relation between curr/next as a list of Bool constraints,
    /// and (2) a concrete curr-state, enumerate ALL satisfying next states.
    pub fn enumerate_next_states_from(
        &self,
        curr_sym: &EnvState<'ctx>,
        next_sym: &EnvState<'ctx>,
        relation_constraints: &[Bool<'ctx>],
        curr_values: &ConcreteState<'ctx>,
    ) -> Vec<ConcreteState<'ctx>> {
        use z3::{Solver, SatResult};
        let ctx = self.ctx;
        let solver = Solver::new(ctx);

        // Scope constraints (domains) — safe to add for both curr and next
        for c in self.generate_scope_constraints_for_state(curr_sym) { solver.assert(&c); }
        for c in self.generate_scope_constraints_for_state(next_sym) { solver.assert(&c); }

        // Relation
        let refs: Vec<&Bool> = relation_constraints.iter().collect();
        solver.assert(&Bool::and(ctx, &refs));

        // Pin current to the provided concrete assignment
        for e in self.pin_curr_equalities(curr_sym, curr_values) { solver.assert(&e); }

        // Enumerate all next-states
        let mut results: Vec<ConcreteState<'ctx>> = Vec::new();
        loop {
            match solver.check() {
                SatResult::Sat => {
                    let m = solver.get_model().expect("model");
                    let next_conc = self.model_to_concrete_next(next_sym, &m);
                    results.push(next_conc.clone());

                    // Block this *next* assignment only (keep curr pinned)
                    let mut disj = Vec::new();
                    for (name, var) in &self.variables {
                        match &var.sort {
                            VarType::Bool { .. } => {
                                let v = bool_var!(next_sym, name);
                                let ConcreteVal::B(b) = next_conc.get(name).unwrap() else { unreachable!() };
                                disj.push(v._eq(&Bool::from_bool(ctx, *b)).not());
                            }
                            VarType::Int { .. } => {
                                let v = int_var!(next_sym, name);
                                let ConcreteVal::I(n) = next_conc.get(name).unwrap() else { unreachable!() };
                                disj.push(v._eq(&Int::from_i64(ctx, *n)).not());
                            }
                            VarType::BVector { .. } => {
                                let v = bv_var!(next_sym, name);
                                let ConcreteVal::BV(n, w) = next_conc.get(name).unwrap() else { unreachable!() };
                                disj.push(v._eq(&BV::from_i64(ctx, *n, *w)).not());
                            }
                        }
                    }
                    let refs2: Vec<&Bool> = disj.iter().collect();
                    solver.assert(&Bool::or(ctx, &refs2));
                }
                SatResult::Unsat => break,
                SatResult::Unknown => {
                    eprintln!("Z3 returned Unknown while enumerating successors; stopping.");
                    break;
                }
            }
        }

        results
    }

    /// Convenience wrapper that uses your registered transitions
    /// instead of passing a custom relation.
    pub fn enumerate_next_states_using_registered_transitions(
        &self,
        curr_sym: &EnvState<'ctx>,
        next_sym: &EnvState<'ctx>,
        curr_values: &ConcreteState<'ctx>,
    ) -> Vec<ConcreteState<'ctx>> {
        let relation = self.generate_transition_relation(curr_sym, next_sym);
        self.enumerate_next_states_from(curr_sym, next_sym, &relation, curr_values)
    }

    /// Canonical key following env.variables order
    fn concrete_to_key(&self, s: &ConcreteState<'ctx>) -> Vec<ConcreteVal> {
        let mut key = Vec::with_capacity(self.variables.len());
        for name in self.variables.keys() {
            key.push(s.get(name).expect("missing var").clone());
        }
        key
    }

    /// Enumerate all initial concrete states (timestamp 0)
    fn enumerate_initial_concrete_states(
        &self,
        sym: &Vec<EnvState<'ctx>>,
    ) -> Vec<ConcreteState<'ctx>> {
        use z3::{Solver, SatResult};
        let ctx = self.ctx;
        let curr = &sym[0];

        let solver = Solver::new(ctx);
        for c in self.generate_scope_constraints_for_state(curr) { solver.assert(&c); }
        for c in self.generate_initial_constraints_for_state(sym, 0) { solver.assert(&c); }

        let mut results = Vec::new();
        loop {
            match solver.check() {
                SatResult::Sat => {
                    let m = solver.get_model().unwrap();
                    let mut conc: ConcreteState<'ctx> = IndexMap::new();
                    for (name, var) in &self.variables {
                        match &var.sort {
                            VarType::Bool { .. } => {
                                let v = bool_var!(curr, name);
                                let b = m.eval(&v, true).unwrap().as_bool().unwrap();
                                conc.insert(*name, ConcreteVal::B(b));
                            }
                            VarType::Int { .. } => {
                                let v = int_var!(curr, name);
                                let n = m.eval(&v, true).unwrap().as_i64().unwrap();
                                conc.insert(*name, ConcreteVal::I(n));
                            }
                            VarType::BVector { width, .. } => {
                                let v = bv_var!(curr, name);
                                let n = m.eval(&v, true).unwrap().as_i64().unwrap();
                                conc.insert(*name, ConcreteVal::BV(n, *width));
                            }
                        }
                    }
                    // block this assignment
                    let mut disj = Vec::new();
                    for (name, var) in &self.variables {
                        match &var.sort {
                            VarType::Bool { .. } => {
                                let v = bool_var!(curr, name);
                                let ConcreteVal::B(b) = conc.get(name).unwrap() else { unreachable!() };
                                disj.push(v._eq(&z3::ast::Bool::from_bool(ctx, *b)).not());
                            }
                            VarType::Int { .. } => {
                                let v = int_var!(curr, name);
                                let ConcreteVal::I(n) = conc.get(name).unwrap() else { unreachable!() };
                                disj.push(v._eq(&z3::ast::Int::from_i64(ctx, *n)).not());
                            }
                            VarType::BVector { .. } => {
                                let v = bv_var!(curr, name);
                                let ConcreteVal::BV(n, w) = conc.get(name).unwrap() else { unreachable!() };
                                disj.push(v._eq(&z3::ast::BV::from_i64(ctx, *n, *w)).not());
                            }
                        }
                    }
                    let refs: Vec<&z3::ast::Bool> = disj.iter().collect();
                    solver.assert(&z3::ast::Bool::or(ctx, &refs));

                    results.push(conc);
                }
                _ => break,
            }
        }
        results
    }

    /// BFS graph construction (no re-expansion; edges always recorded)
    pub fn bfs_build_explicit_graph(&self, suffix: Option<&'ctx str>) -> BFSExplicit<'ctx> {
        // 2 timestamps of symbolic vars: curr, next
        let sym = self.generate_state_variables(1, suffix);
        let curr = &sym[0];
        let next = &sym[1];

        // Build the transition relation once
        let trans_vec = self.generate_transition_relation(curr, next);

        // Initials
        let initials = self.enumerate_initial_concrete_states(&sym);
        assert!(!initials.is_empty(), "No initial states.");

        // Graph storage
        let mut order: Vec<ConcreteState<'ctx>> = Vec::new();
        let mut key_to_idx: HashMap<Vec<ConcreteVal>, usize> = HashMap::new();
        let mut adjacency: Vec<Vec<bool>> = Vec::new();
        let mut edges: Vec<(usize, usize)> = Vec::new();
        let mut expanded: Vec<bool> = Vec::new();
        let mut enqueued: Vec<bool> = Vec::new();

        // Helper that DOES NOT capture outer &muts; we pass them in
        let add_node = |order: &mut Vec<ConcreteState<'ctx>>,
                            key_to_idx: &mut HashMap<Vec<ConcreteVal>, usize>,
                            adjacency: &mut Vec<Vec<bool>>,
                            expanded: &mut Vec<bool>,
                            enqueued: &mut Vec<bool>,
                            st: ConcreteState<'ctx>| -> usize {
            let key = self.concrete_to_key(&st);
            if let Some(&idx) = key_to_idx.get(&key) {
                return idx;
            }
            let idx = order.len();
            order.push(st);
            key_to_idx.insert(key, idx);

            // Grow adjacency matrix
            for row in adjacency.iter_mut() {
                row.push(false);
            }
            adjacency.push(vec![false; order.len()]);

            // Track bookkeeping for the new node
            expanded.push(false);
            enqueued.push(false);

            idx
        };

        // Seed queue
        let mut q: VecDeque<usize> = VecDeque::new();
        for st in initials {
            let idx = add_node(&mut order, &mut key_to_idx, &mut adjacency, &mut expanded, &mut enqueued, st);
            if !enqueued[idx] {
                q.push_back(idx);
                enqueued[idx] = true;
            }
        }

        // BFS
        while let Some(u) = q.pop_front() {
            if expanded[u] { continue; }
            expanded[u] = true;

            // enumerate successors using prebuilt relation
            let succs = self.enumerate_next_states_from(curr, next, &trans_vec, &order[u]);

            for succ in succs {
                let v = add_node(&mut order, &mut key_to_idx, &mut adjacency, &mut expanded, &mut enqueued, succ);

                if !adjacency[u][v] {
                    adjacency[u][v] = true;
                    edges.push((u, v));
                }

                // enqueue only if not yet expanded/enqueued
                if !expanded[v] && !enqueued[v] {
                    q.push_back(v);
                    enqueued[v] = true;
                }
            }
        }

        BFSExplicit { states: order, edges, adjacency }
    }

    pub fn get_predicates(&self) -> &IndexMap<&'ctx str, Box<dyn Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> Bool<'ctx>>> {
        &self.predicates
   }
}
