use std::collections::HashMap;
use z3::{
    ast::{
        Ast, Bool, Dynamic, 
        Int, BV,
    },
    Context,
};

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

#[derive(Debug, Clone)]
pub struct Variable {
    pub sort: VarType,
}

pub type EnvState<'ctx> = HashMap<&'ctx str, Dynamic<'ctx>>;

// #[derive(Debug, Clone)]
pub struct SMVEnv<'ctx> {
    pub ctx: &'ctx Context,
    // The Variable type already has the name. Do we require the name there?
    pub variables: HashMap<&'ctx str, Variable>,
    pub predicates: HashMap<&'ctx str, Box<dyn Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> Bool<'ctx>>>,
    pub transitions: HashMap<&'ctx str, Vec<(Box<dyn Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> ReturnType<'ctx>>, Box<dyn Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> ReturnType<'ctx>>)>>,
}

// Milad: I need this (???)
impl<'ctx> ReturnType<'ctx> {
    pub fn into_dynamic(self, ctx: &'ctx z3::Context, env: &SMVEnv<'ctx>, state: &EnvState<'ctx>, var_name: &str) -> Dynamic<'ctx> {
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
            variables: HashMap::new(),
            predicates: HashMap::new(),
            transitions: HashMap::new(),
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
                                bound_constraints.push(var.bvsge(&BV::from_i64(self.ctx, *v, *width)));
                            }
                            None => ()
                        };
                        match upper {
                            Some(v) => {
                                bound_constraints.push(var.bvsle(&BV::from_i64(self.ctx, *v, *width)));
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

    pub fn generate_transition_relation(& self, curr_state: &EnvState<'ctx>, next_state: &EnvState<'ctx>) -> Vec<Bool> {
        let mut constraints = Vec::new();

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

    pub fn get_transitions(&self) -> &HashMap<&'ctx str, Vec<(Box<dyn Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> ReturnType<'ctx>>, Box<dyn Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> ReturnType<'ctx>>)>> {
        &self.transitions
    }

    pub fn make_dummy_state(&self, ctx: &'ctx z3::Context) -> EnvState<'ctx> {
        let mut state: EnvState<'ctx> = HashMap::new();
 
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
 
    pub fn get_context(&self) -> &'ctx z3::Context {
        self.ctx
    }
 
    pub fn get_variables(&self) -> &HashMap<&'ctx str, Variable> {
        &self.variables
    }
 
    pub fn get_variable_mut(&mut self, name: &str) -> Option<&mut Variable> {
        self.variables.get_mut(name)
    }
 
    pub fn get_variable_type(&self, name: &str) -> Option<&VarType> {
        println!("Looking up variable type for: {}", name);
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



   pub fn get_predicates(&self) -> &HashMap<&'ctx str, Box<dyn Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> Bool<'ctx>>> {
        &self.predicates
   }
}
