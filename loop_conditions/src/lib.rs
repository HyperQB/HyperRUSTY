use std::collections::HashMap;

use z3::{
    ast::{
        Ast, Bool, Dynamic, 
        Int, BV,
    },
    Context,
};
use ir::*;
use enchelper::*;
use hltlunroller::*;
use parser::*;

/// Structure representing loop conditions for hyperLTL verification
/// Used to generate constraints for AE (∀∃) and EA (∃∀) quantifier patterns
pub struct LoopCondition<'env, 'ctx> {
    /// Z3 context for creating constraints
    pub ctx: &'ctx Context,
    /// First SMV model (usually the specification)
    pub model1: &'env SMVEnv<'ctx>,
    /// Second SMV model (usually the implementation)
    pub model2: &'env SMVEnv<'ctx>,
    /// Symbolic states for model1
    pub symstates1: Vec<EnvState<'ctx>>,
    /// Symbolic states for model2
    pub symstates2: Vec<EnvState<'ctx>>,
    /// Simulation variables - sim_i_j[i*m + j] represents simulation between state i of model1 and state j of model2
    pub sim_i_j: Vec<Bool<'ctx>>,
}

impl<'env, 'ctx> LoopCondition<'env, 'ctx> {
    /// Creates a new LoopCondition instance
    /// Generates symbolic states for both models and creates simulation variables
    pub fn new(ctx: &'ctx Context, model1: &'env SMVEnv<'ctx>, model2: &'env SMVEnv<'ctx>) -> Self {
        // Generate symbolic states with prefixes to distinguish between models
        let symstates1 = model1.generate_all_symbolic_states(Some("m1"));
        let symstates2 = model2.generate_all_symbolic_states(Some("m2"));

        // Create simulation variables for each pair of states
        let mut sim_i_j = Vec::new();
        for i in 0..symstates1.len() {
            for j in 0..symstates2.len() {
                sim_i_j.push(Bool::new_const(&ctx, format!("sim_{}_{}", i, j)));
            }
        }       
        Self {
            ctx,
            model1,
            model2,
            symstates1,
            symstates2,
            sim_i_j,
        }
    }

    /// Generates constraints ensuring all symbolic states are legal/valid
    /// Includes scope constraints for variables and initial state constraints
    pub fn legal_state(&self) -> Vec<Bool> {
        let mut valid_states = Vec::new();
        
        // Add scope constraints for model1 states (variable bounds, types, etc.)
        for symstate in &self.symstates1 {
            let constraints = self.model1.generate_scope_constraints_for_state(symstate);
            valid_states.extend(constraints);
        }
        
        // Add scope constraints for model2 states
        for symstate in &self.symstates2 {
            let constraints = self.model2.generate_scope_constraints_for_state(symstate);
            valid_states.extend(constraints);
        }
        
        // Add initial state constraints for both models
        valid_states.extend(self.model1.generate_initial_constraints(&self.symstates1));
        valid_states.extend(self.model2.generate_initial_constraints(&self.symstates2));
        
        valid_states
    }

    /// Generates exhaustive exploration constraints ensuring distinct states are distinguishable
    /// For each pair of different states, they must differ in at least one variable value
    /// is_q: true for model2 (quantifier model), false for model1
    pub fn exhaustive_exploration(&self, is_q: bool) -> Vec<Bool> {
        let (model, symstates) = if is_q {
            (&self.model2, &self.symstates2)
        } else {
            (&self.model1, &self.symstates1)
        };

        let mut constraints = Vec::new();
        // For each pair of distinct states
        for i in 0..symstates.len() {
            for j in (i + 1)..symstates.len() {
                let si = &symstates[i];
                let sj = &symstates[j];
                
                // Generate scope constraints for state i
                let scope_i = model.generate_scope_constraints_for_state(si);
                let ki = Bool::and(self.ctx, &scope_i.iter().collect::<Vec<_>>());

                // Generate scope constraints for state j
                let scope_j = model.generate_scope_constraints_for_state(sj);
                let kj = Bool::and(self.ctx, &scope_j.iter().collect::<Vec<_>>());

                // Build disjunction of differences between states
                let mut diff = Vec::new();
                for (name, _) in model.get_variables().iter() {
                    if let (Some(bi), Some(bj)) = (si.get(name), sj.get(name)) {
                        diff.push(bi._eq(bj).not()); // Variable values must differ
                    }
                }
                let distinct = Bool::or(self.ctx, &diff.iter().collect::<Vec<_>>());
                let and_expr = Bool::and(self.ctx, &[&ki, &kj]);
                
                // If both states are valid, they must be distinguishable
                constraints.push(and_expr.implies(&distinct));
            }
        }
        constraints
    }

    /// Generates initial state simulation constraints for EA (∃∀) patterns
    /// Ensures that initial states of model1 can be simulated by some initial state of model2
    pub fn initial_state_sim_EA(&self) -> Vec<Bool> {
        let mut constraints = Vec::new();
        
        // Add all initial constraints for model1
        constraints.extend(self.model1.generate_initial_constraints(&self.symstates1));
        
        // For each initial state of model2, if it's valid, then corresponding simulation must hold
        for j in 0..(self.symstates2.len()) {
            let initial_constraints_2 = self.model2.generate_initial_constraints_for_state(&self.symstates2, j);
            let initial_and = Bool::and(self.ctx, &initial_constraints_2.iter().collect::<Vec<_>>());
            constraints.push(initial_and.implies(&self.sim_i_j[j]));
        }
        constraints
    }

    /// Generates initial state simulation constraints for AE (∀∃) patterns
    /// For each initial state of model1, there must exist a corresponding initial state in model2
    pub fn initial_state_sim_AE(&self) -> Vec<Bool> {
        let mut constraints = Vec::new();
        
        for i in 0..self.symstates1.len() {
            // Get initial constraints for state i of model1
            let init_constraint_m1 = self.model1.generate_initial_constraints_for_state(&self.symstates1, i);
            let init_constraint_m1_and = Bool::and(self.ctx, &init_constraint_m1.iter().collect::<Vec<_>>());
            
            // Build disjunction over all possible corresponding states in model2
            let mut inner_formula = Vec::new();
            for j in 0..self.symstates2.len() {
                let mut inner_and = Vec::new();
                let init_constraint_m2 = self.model2.generate_initial_constraints_for_state(&self.symstates2, j);
                inner_and.push(Bool::and(self.ctx, &init_constraint_m2.iter().collect::<Vec<_>>()));
                inner_and.push(self.sim_i_j[i * self.symstates2.len() + j].clone());
                inner_formula.push(Bool::and(self.ctx, &inner_and.iter().collect::<Vec<_>>()));
            }
            let inner_or = Bool::or(self.ctx, &inner_formula.iter().collect::<Vec<_>>());
            
            // If state i is a valid initial state of model1, then simulation must exist
            constraints.push(init_constraint_m1_and.implies(&inner_or));
        }
        constraints
    }

    /// Generates successor constraints for simulation relation
    /// If state x simulates state y, then successors of x must simulate corresponding successors of y
    /// x, x_pr: indices in model1; relationship with model2 states through simulation variables
    pub fn succ_t(&self, x: usize, x_pr: usize) -> Bool {
        let mut constraints = Vec::new();
        let m = self.symstates2.len();
        
        for y in 0..m {
            let mut inner_implication = Vec::new();
            
            // For each possible successor of y in model2
            for y_pr in 0..m {
                let transition = self.model2.generate_transition_relation(&self.symstates2[y], &self.symstates2[y_pr]);
                let transition_constraint: Bool<'_> = Bool::and(self.ctx, &transition.iter().collect::<Vec<_>>());
                // If transition y -> y_pr exists, then simulation x_pr -> y_pr must hold
                inner_implication.push(transition_constraint.implies(&self.sim_i_j[x_pr * m + y_pr]));
            }
            let inner_implication = Bool::and(self.ctx, &inner_implication.iter().collect::<Vec<_>>());
            
            // If simulation x -> y holds, then successor condition must be satisfied
            constraints.push(self.sim_i_j[x * m + y].implies(&inner_implication));
        }
        Bool::and(self.ctx, &constraints.iter().collect::<Vec<&Bool>>())
    }

    /// Generates valid path constraints for EA patterns
    /// Ensures transitions in model1 are valid and successor simulation holds
    pub fn valid_path_EA(&self, n: usize) -> Vec<Bool> {
        let mut constraints = Vec::new();
        
        // For each consecutive pair of states in the path
        for i in 0..(n - 1) {
            let mut transition = self.model1.generate_transition_relation(&self.symstates1[i], &self.symstates1[i + 1]);
            // Add successor simulation constraint
            transition.push(self.succ_t(i, i + 1));
            constraints.extend(transition);
        }
        constraints
    }

    /// Generates loop-back constraints for EA patterns
    /// Ensures that from the last state in the path, we can loop back to some earlier state
    pub fn loop_back_EA(&self, n: usize) -> Bool {
        let mut constraints = Vec::new();
        
        // Try to loop back from state n-1 to any state i in [0, n-1]
        for i in 0..(n) {
            let transition = self.model1.generate_transition_relation(&self.symstates1[n - 1], &self.symstates1[i]);
            let transition_constraint = Bool::and(self.ctx, &transition.iter().collect::<Vec<_>>());
            
            let mut inner_formula = Vec::new();
            inner_formula.push(transition_constraint);
            inner_formula.push(self.succ_t(n - 1, i)); // Simulation must be preserved
            constraints.push(Bool::and(self.ctx, &inner_formula.iter().collect::<Vec<_>>()));
        }
        // At least one loop-back must be possible
        Bool::or(self.ctx, &constraints.iter().collect::<Vec<&Bool>>())
    }

    /// Generates complete simulation constraints for EA patterns
    /// Combines valid paths with loop-back constraints for different path lengths
    pub fn simulation_constrains_EA(&self) -> Bool {
        let mut constrains = Vec::new();
        
        // Try different path lengths from 1 to number of states
        for n in (1..self.symstates1.len()){
            let mut valid_path_constain = self.valid_path_EA(n);
            valid_path_constain.push(self.loop_back_EA(n));
            constrains.push(Bool::and(self.ctx, &valid_path_constain.iter().collect::<Vec<_>>()));
        }
        // At least one path length must work
        Bool::or(self.ctx, &constrains.iter().collect::<Vec<&Bool>>())
    }

    /// Generates simulation pair constraints
    /// Ensures that if states are in simulation relation, their transitions preserve the relation
    pub fn simulation_pairs(&self) -> Vec<Bool> {
        let mut constraints = Vec::new();
        let n = self.symstates1.len();
        let k = self.symstates2.len();
        
        // For each pair of states and their potential successors
        for i in 0..(n){
            for t in 0..(n){
                let transition_x = self.model1.generate_transition_relation(&self.symstates1[i], &self.symstates1[t]);
                let transition_x_constraint = Bool::and(self.ctx, &transition_x.iter().collect::<Vec<_>>());
                
                let mut inner_implication = Vec::new();
                for j in 0..(k){
                    let mut inner_constrains = Vec::new();
                    
                    // For each possible successor in model2
                    for r in 0..(k){
                        let transition_y = self.model2.generate_transition_relation(&self.symstates2[j], &self.symstates2[r]);
                        let transition_y_constraint = Bool::and(self.ctx, &transition_y.iter().collect::<Vec<_>>());
                        
                        let mut inner_and = Vec::new();
                        inner_and.push(transition_y_constraint);
                        inner_and.push(self.sim_i_j[t * k + r].clone()); // Successor simulation
                        inner_constrains.push(Bool::and(self.ctx, &inner_and.iter().collect::<Vec<_>>()));
                    }
                    let inner_constrains = Bool::or(self.ctx, &inner_constrains.iter().collect::<Vec<_>>());
                    
                    // If simulation i -> j holds, then successor condition must be satisfied
                    inner_implication.push(self.sim_i_j[i * k + j].implies(&inner_constrains));
                }
                let inner_implication = Bool::and(self.ctx, &inner_implication.iter().collect::<Vec<_>>());
                
                // If transition i -> t exists, then simulation constraints must hold
                constraints.push(transition_x_constraint.implies(&inner_implication));
            }
        }
        constraints
    }

    /// Evaluates predicates in the formula at specific state indices
    /// Recursively processes the AST to build Z3 constraints
    /// i, j: state indices for model1 and model2 respectively
    /// mapping: maps path identifiers to model indices
    pub fn predicate(&self, formula: &AstNode, i: usize, j: usize, mapping: &HashMap<&str, usize>) -> UnrollingReturn<'ctx> {
        match formula {
            // Handle constant values (numbers, TRUE, FALSE)
            AstNode::Constant {value} => {
                if value.parse::<i64>().is_ok() {
                    let number = value.parse::<i64>().unwrap();
                    return UnrollingReturn::Var(Int::from_i64(self.ctx, number).into());
                }
                if value == "TRUE" {
                    UnrollingReturn::Bool(Bool::from_bool(self.ctx, true))
                }else {
                    UnrollingReturn::Bool(Bool::from_bool(self.ctx, false))
                }
            }
            // Handle unary operators (negation, globally)
            AstNode::UnOp {operator, operand} => {
                match operator {
                        UnaryOperator::Negation => {
                            UnrollingReturn::Bool(self.predicate(operand, i, j, mapping).unwrap_bool().not())
                        }
                        // For globally operator, just evaluate the inner formula (loop condition handles temporal aspect)
                        UnaryOperator::Globally => {
                            UnrollingReturn::Bool(self.predicate(operand, i, j, mapping).unwrap_bool())
                        }
                        _=> panic!("The UnOP in the formula is not supported")
                    }
            }
            // Handle binary operators (equality, conjunction, disjunction, implication)
            AstNode::BinOp { operator, lhs, rhs } => {
                match operator {
                    // Equality between different types (Bool, Int, BitVector)
                    parser::BinOperator::Equality =>  match (
                        self.predicate(lhs, i, j, mapping),
                        self.predicate(rhs, i, j, mapping),
                    ) {
                        (UnrollingReturn::Bool(b1), UnrollingReturn::Bool(b2)) => UnrollingReturn::Bool(b1._eq(&b2)),
                        (UnrollingReturn::Var(v1), UnrollingReturn::Var(v2)) => match (v1.as_int(), v2.as_int()) {
                            (Some(i1), Some(i2)) => UnrollingReturn::Bool(i1._eq(&i2)),
                            _ => match (v1.as_bv(), v2.as_bv()) {
                                (Some(bv1), Some(bv2)) => UnrollingReturn::Bool(bv1._eq(&bv2)),
                                _ => match (v1.as_bool(), v2.as_bool()) {
                                    (Some(varb1), Some(varb2)) => UnrollingReturn::Bool(varb1._eq(&varb2)),
                                    _ =>panic!("Invalid comparison"),
                                }
                            }
                        },
                        _ => panic!("Invalid comparison")
                    }
                    // Logical AND
                    BinOperator::Conjunction => {
                        let lhs_bool = self.predicate(lhs, i, j, mapping).unwrap_bool();
                        let rhs_bool = self.predicate(rhs, i, j, mapping).unwrap_bool();
                        UnrollingReturn::Bool(Bool::and(self.ctx, &[&lhs_bool, &rhs_bool]))
                    }
                    // Logical OR
                    BinOperator::Disjunction => {
                        let lhs_bool = self.predicate(lhs, i, j, mapping).unwrap_bool();
                        let rhs_bool = self.predicate(rhs, i, j, mapping).unwrap_bool();
                        UnrollingReturn::Bool(Bool::or(self.ctx, &[&lhs_bool, &rhs_bool]))
                    }
                    // Logical implication
                    BinOperator::Implication => {
                        let lhs_bool = self.predicate(lhs, i, j, mapping).unwrap_bool();
                        let rhs_bool = self.predicate(rhs, i, j, mapping).unwrap_bool();
                        UnrollingReturn::Bool(lhs_bool.implies(&rhs_bool))
                    }
                _=> panic!("The BinOp in the fomrula is not supported")
                }
            }
            // Handle hyperLTL indexed propositions (e.g., a_state[A], b_state[B])
            AstNode::HIndexedProp { proposition, path_identifier } => {
                let idx: &usize = mapping.get(path_identifier as &str).unwrap();
                match idx {
                    // Path identifier maps to model1
                    0 => UnrollingReturn::Var(self.symstates1[i][proposition as &str].clone()),
                    // Path identifier maps to model2
                    1 => UnrollingReturn::Var(self.symstates2[j][proposition as & str].clone()),
                    _ => panic!("wrong mapping")
                }
            }

        _ => unreachable!()
        }
    }

    /// Generates relation predicate constraints
    /// For each pair of states, if simulation holds, then the inner formula must be satisfied
    pub fn relation_predicate(&self, formula: &AstNode) -> Vec<Bool> {
        let mut constraints = Vec::new();
        
        // For each pair of states from both models
        for i in 0..self.symstates1.len() {
            for j in 0..self.symstates2.len() {
                let paths = vec![
                    self.symstates1.clone(),
                    self.symstates2.clone(),
                ];
                
                // Create mapping from path identifiers to model indices
                let mapping = create_path_mapping(formula, 0);
                
                // Evaluate the inner LTL formula at this state pair
                let relation_pred = self.predicate(inner_ltl(formula), i, j, &mapping).unwrap_bool();
                
                // If simulation holds between states i and j, then the relation predicate must hold
                constraints.push(self.sim_i_j[i * self.symstates2.len() + j].implies(&relation_pred));
            }
        }
        constraints
    }

    /// Main function to build loop condition constraints
    /// Validates the formula and generates appropriate constraints based on quantifier pattern
    pub fn build_loop_condition(&self, formula: &AstNode) -> Bool {
        // Validate that formula starts with G or F (temporal operators)
        if !starts_with_g_or_f(formula) {
            panic!("The formula must start with G or F");
        }
        
        // Validate that formula doesn't contain Until or Release operators
        if !has_no_until_or_release(formula) {
            panic!("The formula must not contain Until or Release operators");
        }
        
        // Detect quantifier pattern (AE or EA)
        let check = detect_quantifier_order(formula);
        match check {
            0 => {
                // Unsupported quantifier pattern
                panic!("The formula must be AE or EA");
            }
            1 => {
                // AE (∀∃) pattern: For all paths in model1, there exists a path in model2
                let mut all_constraints = Vec::new();
                all_constraints.extend(self.legal_state());                    // Basic validity constraints
                all_constraints.extend(self.exhaustive_exploration(false));    // Distinctness for model1
                all_constraints.extend(self.initial_state_sim_AE());          // Initial simulation for AE
                all_constraints.extend(self.simulation_pairs());              // Transition simulation
                all_constraints.extend(self.relation_predicate(formula));     // Formula satisfaction

                let refs: Vec<&Bool> = all_constraints.iter().collect();
                let final_constraint = Bool::and(self.ctx, &refs);
                
                final_constraint
            }
            2 => {
                // EA (∃∀) pattern: There exists a path in model1 for all paths in model2
                let mut all_constraints = Vec::new();
                all_constraints.extend(self.legal_state());                    // Basic validity constraints
                all_constraints.extend(self.exhaustive_exploration(true));     // Distinctness for model2
                all_constraints.extend(self.initial_state_sim_EA());          // Initial simulation for EA
                all_constraints.push(self.simulation_constrains_EA());        // Path-based simulation
                all_constraints.extend(self.relation_predicate(formula));     // Formula satisfaction
                
                let refs: Vec<&Bool> = all_constraints.iter().collect();
                Bool::and(self.ctx, &refs)
            }
            _ => {
                // Any other quantifier pattern is not supported
                panic!("Unsupported quantifier order detected");
            }
        }
    }
}