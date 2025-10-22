use std::fs;
use std::collections::HashMap;
use z3::{
    ast::{
        Ast, Bool, Dynamic, 
        Int, BV, forall_const,
        exists_const
    },
    Config, Context, SatResult, Solver,
};
use parser::{
    UnaryOperator, BinOperator,
    AstNode, parse
};

#[macro_use]
mod macros;

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
    sort: VarType,
}

type EnvState<'ctx> = HashMap<&'ctx str, Dynamic<'ctx>>;

// #[derive(Debug, Clone)]
pub struct SMVEnv<'ctx> {
    ctx: &'ctx Context,
    // The Variable type already has the name. Do we require the name there?
    variables: HashMap<&'ctx str, Variable>,
    predicates: HashMap<&'ctx str, Box<dyn Fn(&EnvState<'ctx>) -> Bool<'ctx>>>,
    transitions: HashMap<&'ctx str, Vec<(Box<dyn Fn(&EnvState<'ctx>) -> ReturnType<'ctx>>, Box<dyn Fn(&EnvState<'ctx>) -> ReturnType<'ctx>>)>>,
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

    pub fn register_predicate(&mut self, name: &'ctx str, f: impl Fn(&EnvState<'ctx>) -> Bool<'ctx> + 'static) {
        self.predicates.insert(name, Box::new(f));
    }

    pub fn register_transition(&mut self, name: &'ctx str, condition: impl Fn(&EnvState<'ctx>) -> ReturnType<'ctx> + 'static, update: impl Fn(&EnvState<'ctx>) -> ReturnType<'ctx> + 'static) {
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

    fn generate_initial_constraints(& self, states: &Vec<EnvState<'ctx>>) -> Vec<Bool> {
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

    fn generate_transition_relation(& self, curr_state: &EnvState<'ctx>, next_state: &EnvState<'ctx>) -> Vec<Bool> {
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
                        let update_body = match update(curr_state) {
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
                        let result = match cond(curr_state) {
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
}


// Creates a mapping of the quantified path variables to their corresponding
// index in the state set.
fn create_hltl_mapping(formula: &AstNode, k: usize) -> HashMap<&str, usize> {
    let mut mapping = HashMap::<&str, usize>::new();
    match formula {
        AstNode::HAQuantifier{identifier, form} |
        AstNode::HEQuantifier{identifier, form} => {
            // Recursively map inner quantifiers.
            mapping.extend(create_hltl_mapping(form, k + 1));
            // Update mapping
            mapping.insert(identifier, k);
            // Return the result
            mapping
        }
        _ => mapping
    }
}

#[derive(Debug, Clone)]
pub enum Semantics {
    Pes,
    Opt,
    Hpes,
    HOpt,
}


pub fn unroll_hltl_formula<'ctx>(ctx: &'ctx Context, formula: &AstNode, paths: &Vec<&Vec<EnvState<'ctx>>>, sem: &Semantics) -> Bool<'ctx> {
    // Create a mapping from path quantifiers to the relevent state
    let mapping = create_hltl_mapping(formula, 0);
    // Sanity check
    if paths.len() != mapping.keys().len() {
        panic!("Number of path quantifiers and provided paths must match");
    }

    // Remove all quantifiers.
    let ltl = inner_ltl(formula);
    unroll_ltl_formula(ctx, ltl, paths, &mapping, 0, sem).unwrap_bool()
}

fn inner_ltl(formula: &AstNode) -> &AstNode {
    match formula {
        AstNode::HAQuantifier{identifier: _, form} |
        AstNode::HEQuantifier{identifier: _, form} => {
            inner_ltl(form)
        }
        _ => formula
    }
}

// Combines the LTL encoding of the formula with valid path conditions
fn generate_inner_encoding<'ctx>(ctx: &'ctx Context, formula: &AstNode, path_encodings: &Vec<Bool<'ctx>>, inner_ltl: Bool<'ctx>, k: usize) -> Bool<'ctx> {
    match formula {
        AstNode::HAQuantifier {form, ..} => path_encodings[k].implies(&generate_inner_encoding(ctx, form, path_encodings, inner_ltl, k + 1)),
        AstNode::HEQuantifier {form, ..} => Bool::and(ctx, &[&path_encodings[k], &generate_inner_encoding(ctx, form, path_encodings, inner_ltl, k + 1)]),
        _ => inner_ltl
    }
}

fn dynamic_vec_to_ast_slice<'ctx>(vars: &Vec<&'ctx Dynamic<'ctx>>) -> Vec<&'ctx dyn Ast<'ctx>> {
    vars.iter().map(|v| *v as &dyn Ast<'ctx>).collect()
}

fn generate_quantified_encoding<'ctx>(ctx: &'ctx Context, formula: &AstNode, paths: &Vec<&Vec<EnvState<'ctx>>>, path_encodings: &Vec<Bool<'ctx>>, mapping: &HashMap<&str, usize>, inner: Bool<'ctx>) -> Bool<'ctx> {
    match formula {
        AstNode::HAQuantifier {form, identifier} => {
            let idx = mapping.get(identifier as &str).unwrap();
            let selected_path = paths[*idx];
            let vars: Vec<Dynamic<'ctx>> = selected_path
                .iter()
                .flat_map(|env| env.values().cloned()) // clones Dynamic<'ctx>
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            // Step 2: Convert to a slice
            let ast_slice: &[&dyn Ast<'ctx>] = &ast_refs;
            forall_const(
                ctx,
                ast_slice,
                &[],
                &generate_quantified_encoding(ctx, form, paths, path_encodings, mapping, inner)
            )
        }
        AstNode::HEQuantifier {form, identifier} => {
            let idx = mapping.get(identifier as &str).unwrap();
            let selected_path = paths[*idx];
            let vars: Vec<Dynamic<'ctx>> = selected_path
                .iter()
                .flat_map(|env| env.values().cloned()) // clones Dynamic<'ctx>
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            // Step 2: Convert to a slice
            let ast_slice: &[&dyn Ast<'ctx>] = &ast_refs;
            exists_const(
                ctx,
                ast_slice,
                &[],
                &generate_quantified_encoding(ctx, form, paths, path_encodings, mapping, inner)
            )
        }
        _ => inner
    }
}

fn generate_hltl_encoding<'ctx>(ctx: &'ctx Context, formula: &AstNode, paths: &Vec<&Vec<EnvState<'ctx>>>, path_encodings: &Vec<Bool<'ctx>>, sem: &Semantics) -> Bool<'ctx> {
    // Unroll the formula first
    let inner_ltl = unroll_hltl_formula(ctx, formula, paths, sem);
    // Construct the inner encoding
    let inner = generate_inner_encoding(ctx, formula, path_encodings, inner_ltl.clone(), 0);
    // Get the mapping
    let mapping = create_hltl_mapping(formula, 0);
    // Build the complete encoding
    generate_quantified_encoding(ctx, formula, paths, path_encodings, &mapping, inner.clone())

}

fn is_halted<'ctx>(ctx: &'ctx Context, paths: &Vec<&Vec<EnvState<'ctx>>>) -> Bool<'ctx> {
    // Checks if `halted` holds on the last state of unrolling
    // Get the unrolling bound (states are not empty)
    let bound = paths[0].len() - 1;
    let mut halt_vars = Vec::<Bool<'ctx>>::new();
    for i in 0..paths.len() {
        // Get the mapping corresponding to the last state
        let final_step = &paths[i][bound];
        //Halted is a boolean variable
        // If the state doesn't have `halt`, panic
        let halt = match final_step.get("halt") {
            Some(node) => node,
            None => panic!("`halt` is not defined on model number {}", i + 1)
        };
        // It's a dynamic variable, so it needs to be cast as a Boolean
        halt_vars.push(halt.as_bool().unwrap());
    }
    let refs: Vec<&Bool> = halt_vars.iter().collect();
    Bool::and(ctx, &refs)
}

enum UnrollingReturn<'ctx> {
    Bool(Bool<'ctx>),
    Var(Dynamic<'ctx>),
}

impl<'ctx> UnrollingReturn<'ctx> {
    pub fn unwrap_bool(self) -> Bool<'ctx> {
        match self {
            UnrollingReturn::Bool(b) => b,
            _ => panic!("Expected UnrollingReturn::Bool type"),
        }
    }
}

fn unroll_ltl_formula<'ctx>(ctx: &'ctx Context, formula: &AstNode, paths: &Vec<&Vec<EnvState<'ctx>>>, mapping: &HashMap<&str, usize>, k: usize, sem: &Semantics) -> UnrollingReturn<'ctx> {
    let bound = paths[0].len() - 1;
    match formula {
        AstNode::UnOp {operator, operand} => {
            match operator {
                UnaryOperator::Negation => {
                    UnrollingReturn::Bool(unroll_ltl_formula(ctx, operand, paths, mapping, k, sem).unwrap_bool().not())
                }
                UnaryOperator::Globally => {
                    let mut constraints = Vec::new();
                    for i in k..=bound {
                        constraints.push(unroll_ltl_formula(ctx, operand, paths, mapping, i, sem).unwrap_bool());
                    }
                    let refs: Vec<&Bool> = constraints.iter().collect();
                    UnrollingReturn::Bool(Bool::and(ctx, &refs))
                }
                UnaryOperator::Eventually => {
                    let mut constraints = Vec::new();
                    for i in k..=bound {
                        constraints.push(unroll_ltl_formula(ctx, operand, paths, mapping, i, sem).unwrap_bool());
                    }
                    let refs: Vec<&Bool> = constraints.iter().collect();
                    UnrollingReturn::Bool(Bool::or(ctx, &refs))
                }
                UnaryOperator::Next => {
                    if k != bound {
                        // We are not on the final state, so we can continue
                        unroll_ltl_formula(ctx, operand, paths, mapping, k + 1, sem)
                    }else {
                        match sem {
                            Semantics::Pes => UnrollingReturn::Bool(Bool::from_bool(ctx, false)),
                            Semantics::Opt => UnrollingReturn::Bool(Bool::from_bool(ctx, true)),
                            Semantics::Hpes => {
                                let halted = is_halted(ctx, paths);
                                let eval_result = unroll_ltl_formula(ctx, operand, paths, mapping, k, sem).unwrap_bool();
                                UnrollingReturn::Bool(Bool::and(ctx, &[&halted, &eval_result]))
                            }
                            Semantics::HOpt => {
                                let not_halted = is_halted(ctx, paths).not();
                                let eval_result = unroll_ltl_formula(ctx, operand, paths, mapping, k, sem).unwrap_bool();
                                UnrollingReturn::Bool(Bool::or(ctx, &[&not_halted, &eval_result]))
                            }
                        }
                    }
                }
            }
        }
        AstNode::BinOp {operator, lhs, rhs} => {
            match operator {
                BinOperator::Equality => {
                    match (
                        unroll_ltl_formula(ctx, lhs, paths, mapping, k, sem),
                        unroll_ltl_formula(ctx, rhs, paths, mapping, k, sem),
                    ) {
                        (UnrollingReturn::Bool(b1), UnrollingReturn::Bool(b2)) => UnrollingReturn::Bool(b1._eq(&b2)),
                        (UnrollingReturn::Var(v1), UnrollingReturn::Var(v2)) => match (v1.as_int(), v2.as_int()) {
                            (Some(i1), Some(i2)) => UnrollingReturn::Bool(i1._eq(&i2)),
                            _ => match (v1.as_bv(), v2.as_bv()) {
                                (Some(bv1), Some(bv2)) => UnrollingReturn::Bool(bv1._eq(&bv2)),
                                _ => panic!("Invalid comparison"),
                            }
                        },
                        _ => panic!("Invalid comparison")
                    }
                }
                BinOperator::Conjunction => {
                    let lhs_bool = unroll_ltl_formula(ctx, lhs, paths, mapping, k, sem).unwrap_bool();
                    let rhs_bool = unroll_ltl_formula(ctx, rhs, paths, mapping, k, sem).unwrap_bool();
                    UnrollingReturn::Bool(Bool::and(ctx, &[&lhs_bool, &rhs_bool]))
                }
                BinOperator::Disjunction => {
                    let lhs_bool = unroll_ltl_formula(ctx, lhs, paths, mapping, k, sem).unwrap_bool();
                    let rhs_bool = unroll_ltl_formula(ctx, rhs, paths, mapping, k, sem).unwrap_bool();
                    UnrollingReturn::Bool(Bool::or(ctx, &[&lhs_bool, &rhs_bool]))
                }
                BinOperator::Implication => {
                    let lhs_bool = unroll_ltl_formula(ctx, lhs, paths, mapping, k, sem).unwrap_bool();
                    let rhs_bool = unroll_ltl_formula(ctx, rhs, paths, mapping, k, sem).unwrap_bool();
                    UnrollingReturn::Bool(lhs_bool.implies(&rhs_bool))
                }
            }
        }
        AstNode::HIndexedProp {proposition, path_identifier} => {
            // If proposition is not defined, panic!
            // Always exists
            let idx: &usize = mapping.get(path_identifier as &str).unwrap();
            let curr_state = &paths[*idx][k];
            match curr_state.get(proposition as &str) {
                Some(v) => {
                    if let Some(node) = v.as_bool() {
                        return UnrollingReturn::Bool(node)
                    }else {
                        return UnrollingReturn::Var(v.clone())
                    }
                }
                None => panic!("Udnefined variable {}", proposition)
            }
        }
        _ => unreachable!()
    }
}


fn main() {

    // Bring in the source
    let source = fs::read_to_string("formula.hq").expect("Failed to read source");

    let ast_node = parse(&source).expect("Input parsing failed");

    let mut cfg = Config::new();
    cfg.set_model_generation(true);
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let mut env = SMVEnv::new(&ctx);

    env.register_variable("a", VarType::Bool {init: Some(vec![true])});

    env.register_transition("a",
    |_state| exact!(Node, bool_var!(_state, "a")),
    |_state| exact!(Bool, false)
    );
    env.register_transition("a",
    |_state| exact!(Node, !bool_var!(_state, "a")),
    |_state| exact!(Bool, true)
    );

    let (states, sym_path) = env.generate_symbolic_path(2, Some("A"));

    let form = generate_hltl_encoding(&ctx, &ast_node, &vec![&states], &vec![sym_path], &Semantics::Pes);

    // println!("{:?}", form);

    solver.assert(&form);

    match solver.check() {
        SatResult::Sat => {
            println!("result: sat.");
        },
        SatResult::Unsat => {
            println!("result: unsat.");
        },
        SatResult::Unknown => {
            println!("result: unknown.");
        }
    };

}