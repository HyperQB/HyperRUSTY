use std::{collections::HashMap, pin, usize};

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
use expressions::*;
use std::io::Write as IoWrite;
use unroller_qbf::*;
use fsm::helper_functions::create_file;



fn adj_bool_to_z3<'ctx>(ctx: &'ctx Context, adj: &Vec<Vec<bool>>) -> Vec<Vec<Bool<'ctx>>> {
    adj.iter()
        .map(|row| row.iter().map(|&b| Bool::from_bool(ctx, b)).collect())
        .collect()
}


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
    // Concrete values returned by BFS (explicit values) m1
    pub vals1: Vec<ConcreteState<'ctx>>,
    /// m2
    pub vals2: Vec<ConcreteState<'ctx>>,
    /// Simulation variables - sim_i_j[i*m + j] represents simulation between state i of model1 and state j of model2
    pub sim_i_j: Vec<Vec<Bool<'ctx>>>,
    /// Transition relation for model 1
    pub trans_i_ipr: Vec<Vec<Bool<'ctx>>>,
    /// Transition relation for model 2
    pub trans_j_jpr: Vec<Vec<Bool<'ctx>>>
}


impl<'env, 'ctx> LoopCondition<'env, 'ctx> {


    pub fn new(ctx: &'ctx Context, model1: &'env SMVEnv<'ctx>, model2: &'env SMVEnv<'ctx>) -> Self {
        Self {
            ctx,
            model1,
            model2,
            symstates1: Vec::new(),
            symstates2: Vec::new(),
            vals1: Vec::new(),
            vals2: Vec::new(),
            trans_i_ipr: Vec::new(),
            trans_j_jpr: Vec::new(),
            sim_i_j: Vec::new(),
        }
    }

    pub fn init_AE(&mut self) {
        let g1 = self.model1.bfs_build_explicit_graph(Some("m1"));
        let g2 = self.model2.bfs_build_explicit_graph(Some("m2"));

        self.vals1 = g1.states;              // Vec<ConcreteState>
        self.trans_i_ipr = adj_bool_to_z3(self.ctx, &g1.adjacency);     // Vec<Vec<bool>>

        self.vals2 = g2.states;              // Vec<ConcreteState>
        self.trans_j_jpr = adj_bool_to_z3(self.ctx, &g2.adjacency);     // Vec<Vec<bool>>

        // Create matching symbolic snapshots (one per explicit state)
        self.symstates1 = Vec::with_capacity(self.vals1.len());
        for i in 0..self.vals1.len() {
            self.symstates1.push(self.model1.make_enum_dummy_state(self.ctx, i, 1));
        }
        self.symstates2 = Vec::with_capacity(self.vals2.len());
        for i in 0..self.vals2.len() {
            self.symstates2.push(self.model2.make_enum_dummy_state(self.ctx, i, 2));
        }

        // sim[i][j]
        self.sim_i_j = Vec::with_capacity(self.vals1.len());
        for i in 0..self.vals1.len() {
            let mut row = Vec::with_capacity(self.vals2.len());
            for j in 0..self.vals2.len() {
                row.push(Bool::new_const(self.ctx, format!("sim_{}_{}", i, j)));
            }
            self.sim_i_j.push(row);
        }
    }

    pub fn init_EA(&mut self){
        // Generate symbolic states with prefixes to distinguish between models
        self.symstates1 = self.model1.generate_all_symbolic_states(Some("m1"));
        self.symstates2 = self.model2.generate_all_symbolic_states( Some("m2"));

        // sim[i][j]
        self.sim_i_j = Vec::with_capacity(self.symstates1.len());
        for i in 0..self.symstates1.len() {
            let mut row = Vec::with_capacity(self.symstates2.len());
            for j in 0..self.symstates2.len() {
                row.push(Bool::new_const(self.ctx, format!("sim_{}_{}", i, j)));
            }
            self.sim_i_j.push(row);
        }
        //println!("{:#?}", self.sim_i_j);
    }







    fn pin_state_eq(&self, env: &SMVEnv<'ctx>, sym: &EnvState<'ctx>, conc: &ConcreteState<'ctx>, idx: usize) -> Vec<Bool<'ctx>> {
        let mut cs = Vec::<Bool>::new();
        for (name, var) in env.get_variables().iter() {
            let base = format!("{name}_{idx}");
            match (&var.sort, conc.get(name).expect("missing concrete value")) {
                (VarType::Bool{..}, ConcreteVal::B(b)) => {
                    let v = bool_var!(sym, name);
                    cs.push(v._eq(&Bool::from_bool(self.ctx, *b)));
                }
                (VarType::Int{..}, ConcreteVal::I(n)) => {
                    let v = int_var!(sym, name);
                    cs.push(v._eq(&Int::from_i64(self.ctx, *n)));
                }
                (VarType::BVector{width, ..}, ConcreteVal::BV(n, w)) => {
                    assert_eq!(*width, *w, "BV width mismatch for {}", name);
                    let v = bv_var!(sym, name);
                    cs.push(v._eq(&BV::from_i64(self.ctx, *n, *w)));
                }
                _ => panic!("type mismatch while pinning {}", name),
            }
        }
        cs
    }

    /// Pins *all* snapshots in both models to the BFS concrete values.
    pub fn pin_all_explicit_states(&self) -> Vec<Bool<'ctx>> {
        let mut out = Vec::<Bool>::new();

        // Model 1
        for i in 0..self.symstates1.len() {
            out.extend(self.pin_state_eq(self.model1, &self.symstates1[i], &self.vals1[i], i));
        }
        // Model 2
        for i in 0..self.symstates2.len() {
            out.extend(self.pin_state_eq(self.model2, &self.symstates2[i], &self.vals2[i], i));
        }
        //println!("{:#?}", out);
        out
    }


    pub fn legal_explicit_state(&self) -> Vec<Bool<'env>>{
        self.pin_all_explicit_states()
    }
        /// Generates constraints ensuring all symbolic states are legal/valid
    /// Includes scope constraints for variables and initial state constraints
    pub fn legal_state(&self) -> Vec<Bool<'env>> {
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
    pub fn exhaustive_exploration(&self, is_q: bool) -> Vec<Bool<'env>> {
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
    pub fn initial_state_sim_EA(&self) -> Vec<Bool<'env>> {
        let mut constraints = Vec::new();
        
        // Add all initial constraints for model1
        constraints.extend(self.model1.generate_initial_constraints(&self.symstates1));
        
        // For each initial state of model2, if it's valid, then corresponding simulation must hold
        for j in 0..(self.symstates2.len()) {
            let initial_constraints_2 = self.model2.generate_initial_constraints_for_state(&self.symstates2, j);
            let initial_and = Bool::and(self.ctx, &initial_constraints_2.iter().collect::<Vec<_>>());
            constraints.push(initial_and.implies(&self.sim_i_j[0][j]));
        }
        //println!("{:#?}", constraints);
        constraints
    }

    /// Generates initial state simulation constraints for AE (∀∃) patterns
    /// For each initial state of model1, there must exist a corresponding initial state in model2
    pub fn initial_state_sim_AE(&self) -> Vec<Bool<'env>> {
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
                inner_and.push(self.sim_i_j[i][j].clone());
                inner_formula.push(Bool::and(self.ctx, &inner_and.iter().collect::<Vec<_>>()));
            }
            let inner_or = Bool::or(self.ctx, &inner_formula.iter().collect::<Vec<_>>());
            
            // If state i is a valid initial state of model1, then simulation must exist
            constraints.push(init_constraint_m1_and.implies(&inner_or));
        }
        //println!("{:#?}", constraints);
        constraints
    }

     /// Generates successor constraints for simulation relation
    /// If state x simulates state y, then successors of x must simulate corresponding successors of y
    /// x, x_pr: indices in model1; relationship with model2 states through simulation variables
    pub fn succ_t(&self, x: usize, x_pr: usize) -> Bool<'env> {
        let mut constraints = Vec::new();
        let m = self.symstates2.len();
        
        for y in 0..m {
            let mut inner_implication = Vec::new();
            
            // For each possible successor of y in model2
            for y_pr in 0..m {
                let transition = self.model2.generate_transition_relation(&self.symstates2[y], &self.symstates2[y_pr]);
                let transition_constraint: Bool<'_> = Bool::and(self.ctx, &transition.iter().collect::<Vec<_>>());
                // If transition y -> y_pr exists, then simulation x_pr -> y_pr must hold
                inner_implication.push(transition_constraint.implies(&self.sim_i_j[x_pr][y_pr]));
            }
            let inner_implication = Bool::and(self.ctx, &inner_implication.iter().collect::<Vec<_>>());
            
            // If simulation x -> y holds, then successor condition must be satisfied
            constraints.push(self.sim_i_j[x][y].implies(&inner_implication));
        }
        Bool::and(self.ctx, &constraints.iter().collect::<Vec<&Bool>>())
    }

    /// Generates valid path constraints for EA patterns
    /// Ensures transitions in model1 are valid and successor simulation holds
    pub fn valid_path_EA(&self, n: usize) -> Vec<Bool<'env>> {
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
    pub fn loop_back_EA(&self, n: usize) -> Bool<'env> {
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
    pub fn simulation_constrains_EA(&self) -> Bool<'env> {
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
    pub fn simulation_constrains_AE(&self) -> Vec<Bool<'env>> {
        let mut constraints = Vec::new();
        let n = self.symstates1.len(); // M1 states
        let k = self.symstates2.len(); // M2 states


        for i in 0..n {
            for t in 0..n {
                let tx = self.trans_i_ipr[i][t].clone(); // MUST be M1(i→t)
                let mut per_j = Vec::new();
                for j in 0..k {
                    // ∃r. (j→r in M2) ∧ sim(t,r)
                    let mut exists_r = Vec::new();
                    for r in 0..k {
                        let ty = self.trans_j_jpr[j][r].clone(); // MUST be M2(j→r)
                        exists_r.push(Bool::and(self.ctx, &[&ty, &self.sim_i_j[t][r]]));
                    }
                    let exists_r = Bool::or(self.ctx, &exists_r.iter().collect::<Vec<_>>());
                    per_j.push(self.sim_i_j[i][j].implies(&exists_r));
                }
                let per_j = Bool::and(self.ctx, &per_j.iter().collect::<Vec<_>>());
                constraints.push(tx.implies(&per_j));
            }
        }
        // println!("Simulation pairs");
        // println!("{:#?}", constraints);
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
                match operator {                    // Equality between different types (Bool, Int, BitVector)
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
                // get idx (&usize -> usize)
                let idx = *mapping
                    .get(path_identifier.as_str())
                    .expect("missing path_identifier in mapping");

                // choose the state/env once, keep them alive after the match
                let (curr_state, env) = match idx {
                    0 => (&self.symstates1[i], &self.model1),
                    1 => (&self.symstates2[j], &self.model2),
                    _ => panic!("wrong mapping"),
                };

                // then use them
                if let Some(v) = curr_state.get(proposition.as_str()) {
                    if let Some(node) = v.as_bool() {
                        UnrollingReturn::Bool(node)
                    } else {
                        UnrollingReturn::Var(v.clone())
                    }
                } else {
                    match env.predicates.get(proposition.as_str()) {
                        Some(predicate) => {
                            // assuming signature like: fn(&Env, Ctx, &State) -> bool
                            let clause = predicate(env, self.ctx, curr_state);
                            UnrollingReturn::Bool(clause)
                        }
                        None => panic!("Undefined variable or predicate `{}`", proposition),
                    }
                }
            }
            _ => unreachable!()
        }
    }

    /// Generates relation predicate constraints
    /// For each pair of states, if simulation holds, then the inner formula must be satisfied
    pub fn relation_predicate(&self, formula: &AstNode) -> Vec<Bool<'env>> {
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
                constraints.push(self.sim_i_j[i][j].implies(&relation_pred));
            }
        }
        //  println!("{:#?}", constraints);
        constraints
    }

    /// Main function to build loop condition constraints
    /// Validates the formula and generates appropriate constraints based on quantifier pattern
    pub fn build_loop_condition(&mut self, formula: &AstNode) -> Bool<'env> {
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
                self.init_AE();
                let mut all_constraints = Vec::new();
                all_constraints.extend(self.legal_explicit_state());
                all_constraints.extend(self.exhaustive_exploration(false));
                all_constraints.extend(self.initial_state_sim_AE());
                all_constraints.extend(self.simulation_constrains_AE());              // Transition simulation
                all_constraints.extend(self.relation_predicate(formula));     // Formula satisfaction

                // Create references vector in the same scope as Bool::and
                let refs: Vec<&Bool> = all_constraints.iter().collect();
                Bool::and(self.ctx, &refs)
            }
            2 => {
                // EA (∃∀) pattern: There exists a path in model1 for all paths in model2
                self.init_EA();
                let mut all_constraints = Vec::new();
                all_constraints.extend(self.legal_state());     
                all_constraints.extend(self.exhaustive_exploration(true));
                all_constraints.extend(self.initial_state_sim_EA());          // Initial simulation for EA
                all_constraints.push(self.simulation_constrains_EA());        // Path-based simulation
                all_constraints.extend(self.relation_predicate(formula));     // Formula satisfaction
                let refs: Vec<&Bool<'env>> = all_constraints.iter().collect();
                Bool::and(self.ctx, &refs)
            }
            _ => {
                // Any other quantifier pattern is not supported
                panic!("Unsupported quantifier order detected");
            }
        }
    }



}