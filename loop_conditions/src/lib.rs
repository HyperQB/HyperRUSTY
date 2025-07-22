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
use parser::AstNode;


pub struct LoopCondition<'ctx> {
    pub ctx: &'ctx Context,
    pub model1: SMVEnv<'ctx>,
    pub model2: SMVEnv<'ctx>,
    pub symstates1: Vec<EnvState<'ctx>>,
    pub symstates2: Vec<EnvState<'ctx>>,
    pub sim_i_j: Vec<Bool<'ctx>>,
}

impl<'ctx> LoopCondition<'ctx> {
    pub fn new(ctx: &'ctx Context, model1: SMVEnv<'ctx>, model2: SMVEnv<'ctx>) -> Self {
        let symstates1 = model1.generate_all_symbolic_states(Some("m1"));
        let symstates2 = model2.generate_all_symbolic_states(Some("m2"));

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


    pub fn legal_state(&self) -> Vec<Bool> {
        let mut valid_states = Vec::new();
        
        for symstate in &self.symstates1 {
            let constraints = self.model1.generate_scope_constraints_for_state(symstate);
            valid_states.extend(constraints);
        }
        
        for symstate in &self.symstates2 {
            let constraints = self.model2.generate_scope_constraints_for_state(symstate);
            valid_states.extend(constraints);
        }

        valid_states
    }

    pub fn exhaustive_exploration(&self, is_q: bool) -> Vec<Bool> {
        let (model, symstates) = if is_q {
            (&self.model2, &self.symstates2)
        } else {
            (&self.model1, &self.symstates1)
        };

        let mut constraints = Vec::new();
        for i in 0..symstates.len() {
            for j in (i + 1)..symstates.len() {
                let si = &symstates[i];
                let sj = &symstates[j];
                
                let scope_i = model.generate_scope_constraints_for_state(si);
                let ki = Bool::and(self.ctx, &scope_i.iter().collect::<Vec<_>>());

                let scope_j = model.generate_scope_constraints_for_state(sj);
                let kj = Bool::and(self.ctx, &scope_j.iter().collect::<Vec<_>>());

                let mut diff = Vec::new();
                for (name, _) in model.get_variables().iter() {
                    if let (Some(bi), Some(bj)) = (si.get(name), sj.get(name)) {
                        diff.push(bi._eq(bj).not());
                    }
                }
                let distinct = Bool::or(self.ctx, &diff.iter().collect::<Vec<_>>());
                let and_expr = Bool::and(self.ctx, &[&ki, &kj]);
                constraints.push(and_expr.implies(&distinct));
            }
        }
        constraints
    }


    pub fn initial_state_sim_EA(&self) -> Vec<Bool> {
        let mut constraints = Vec::new();
        constraints.extend(self.model1.generate_initial_constraints(&self.symstates1));
        for j in 0..self.symstates2.len() {
            let initial_constraints_2 = self.model2.generate_initial_constraints(&self.symstates2);
            let initial_and = Bool::and(self.ctx, &initial_constraints_2.iter().collect::<Vec<_>>());
            constraints.push(initial_and.implies(&self.sim_i_j[j]));
        }
        constraints
    }

    pub fn initial_state_sim_AE(&self) -> Vec<Bool> {
        let mut constraints = Vec::new();
        for i in 0..self.symstates1.len() {
            let init_constraint_m1 = self.model1.generate_initial_constraints(&self.symstates1);
            let init_constraint_m1_and = Bool::and(self.ctx, &init_constraint_m1.iter().collect::<Vec<_>>());
            let mut inner_formula = Vec::new();
            for j in 0..self.symstates2.len() {
                let mut inner_and = Vec::new();
                let init_constraint_m2 = self.model2.generate_initial_constraints(&self.symstates2);
                inner_and.push(Bool::and(self.ctx, &init_constraint_m2.iter().collect::<Vec<_>>()));
                inner_and.push(self.sim_i_j[i * self.symstates2.len() + j].clone());
                inner_formula.push(Bool::and(self.ctx, &inner_and.iter().collect::<Vec<_>>()));
            }
            let inner_or = Bool::or(self.ctx, &inner_formula.iter().collect::<Vec<_>>());
            constraints.push(init_constraint_m1_and.implies(&inner_or));
        }
        constraints
    }


    pub fn succ_t(&self, x: usize, x_pr: usize) -> Bool {
        let mut constraints = Vec::new();
        let m = self.symstates2.len();
        for y in 0..m {
            for y_pr in 0..m {
                let transition = self.model2.generate_transition_relation(&self.symstates2[y], &self.symstates2[y_pr]);
                let transition_constraint = Bool::and(self.ctx, &transition.iter().collect::<Vec<_>>());
                let inner_implication = transition_constraint.implies(&self.sim_i_j[x_pr * m + y_pr]);
                constraints.push(self.sim_i_j[x * m + y].implies(&inner_implication));
            }
        }
        Bool::and(self.ctx, &constraints.iter().collect::<Vec<&Bool>>())
    }

    pub fn valid_path_EA(&self) -> Vec<Bool> {
        let mut constraints = Vec::new();
        for i in 0..(self.symstates1.len() - 1) {
            let mut transition = self.model1.generate_transition_relation(&self.symstates1[i], &self.symstates1[i + 1]);
            transition.push(self.succ_t(i, i + 1));
            constraints.extend(transition);
        }
        constraints
    }

    pub fn loop_back_EA(&self) -> Bool {
        let mut constraints = Vec::new();
        let n = self.symstates1.len();
        for i in 0..(n) {
            let transition = self.model1.generate_transition_relation(&self.symstates1[n], &self.symstates1[i]);
            let transition_constraint = Bool::and(self.ctx, &transition.iter().collect::<Vec<_>>());
            let mut inner_formula = Vec::new();
            inner_formula.push(transition_constraint);
            inner_formula.push(self.succ_t(n, i));
            constraints.push(Bool::and(self.ctx, &inner_formula.iter().collect::<Vec<_>>()));
        }
        Bool::or(self.ctx, &constraints.iter().collect::<Vec<&Bool>>())
    }

    pub fn simulation_pairs(&self) -> Vec<Bool> {
        let mut constraints = Vec::new();
        let n = self.symstates1.len();
        let k = self.symstates2.len();
        for i in 0..(n){
            for t in 0..(n){
                let transition_x = self.model1.generate_transition_relation(&self.symstates1[i], &self.symstates2[t]);
                let transition_x_constraint = Bool::and(self.ctx, &transition_x.iter().collect::<Vec<_>>());
                let mut inner_implication = Vec::new();
                for j in 0..(k){
                    let mut inner_constrains = Vec::new();
                    for r in 0..(k){
                        let transition_y = self.model2.generate_transition_relation(&self.symstates2[j], &self.symstates2[r]);
                        let transition_y_constraint = Bool::and(self.ctx, &transition_y.iter().collect::<Vec<_>>());
                        let mut inner_and = Vec::new();
                        inner_and.push(transition_y_constraint);
                        inner_and.push(self.sim_i_j[t * k + r].clone());
                        inner_constrains.push(Bool::and(self.ctx, &inner_and.iter().collect::<Vec<_>>()));
                    }
                    let inner_constrains = Bool::or(self.ctx, &inner_constrains.iter().collect::<Vec<_>>());
                    inner_implication.push(self.sim_i_j[i * k + j].implies(&inner_constrains));
                }
                let inner_implication = Bool::and(self.ctx, &inner_implication.iter().collect::<Vec<_>>());
                constraints.push(transition_x_constraint.implies(&inner_implication));
            }
        }
        constraints
    }


     
    pub fn relation_predicate(&self, formula: &AstNode) -> Vec<Bool> {
        let mut constraints = Vec::new();
        for i in 0..self.symstates1.len() {
            for j in 0..self.symstates2.len() {
                let paths = vec![
                    self.symstates1.clone(),
                    self.symstates2.clone(),
                ];
                let relation_pred = unroll_hltl_formula(
                    self.ctx, 
                    formula, 
                    &paths, 
                    &Semantics::Opt,
                );
                constraints.push(self.sim_i_j[i * self.symstates2.len() + j].implies(&relation_pred));
            }
        }
        constraints
    }

    pub fn build_loop_condition(&self, formula: &AstNode) -> Bool {
        // Check if formula starts with G/F
        if !starts_with_g_or_f(formula) {
            panic!("The formula must start with G or F");
        }
        // Check that formula doesn't have Until or Release
        if !has_no_until_or_release(formula) {
            panic!("The formula must not contain Until or Release operators");
        }
        // First we check that if formula is AE or EA
        let check = detect_quantifier_order(formula);
        match check {
            0 => {
                // If the formula is not AE or EA, return false
                panic!("The formula must be AE or EA");
            }
            1 => {
                // If the formula is AE, build the loop condition for AE
                let mut all_constraints = Vec::new();
                all_constraints.extend(self.legal_state());
                all_constraints.extend(self.exhaustive_exploration(false));
                all_constraints.extend(self.initial_state_sim_AE());
                all_constraints.extend(self.simulation_pairs());
                all_constraints.extend(self.relation_predicate(formula));

                let refs: Vec<&Bool> = all_constraints.iter().collect();
                Bool::and(self.ctx, &refs)
            }
            2 => {
                // If the formula is EA, build the loop condition for EA
                let mut all_constraints = Vec::new();
                all_constraints.extend(self.legal_state());
                all_constraints.extend(self.exhaustive_exploration(true));
                all_constraints.extend(self.initial_state_sim_EA());
                all_constraints.extend(self.valid_path_EA());
                all_constraints.push(self.loop_back_EA());
                all_constraints.extend(self.relation_predicate(formula));
                
                let refs: Vec<&Bool> = all_constraints.iter().collect();
                Bool::and(self.ctx, &refs)
            }
            _ => {
                // If the formula has an unsupported quantifier order, return false
                panic!("Unsupported quantifier order detected");
            }
        }
    }


}