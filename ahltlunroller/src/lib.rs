use std::collections::HashMap;
use ir::*;
use enchelper::*;
use z3::{Context,
    ast::{
        Ast, Dynamic, Bool,
    }
};
use parser::{
    UnaryOperator, BinOperator,
    AstNode,
};

pub struct AHLTLObject<'env, 'ctx> {
    pub envs: &'env Vec<SMVEnv<'ctx>>,
    pub states: Vec<Vec<EnvState<'ctx>>>,
    pub formula: &'ctx AstNode,
    pub k: usize,
    pub m: usize,
    pub paths: Vec<&'ctx str>,
    pub trajs: Vec<&'ctx str>,
    pub path_mappings: HashMap<&'ctx str, usize>,
    pub positions: HashMap<&'ctx str, HashMap<&'ctx str, HashMap<String, Bool<'ctx>>>>,
    pub trajectories: HashMap<&'ctx str, HashMap<&'ctx str, Vec<Bool<'ctx>>>>,
    pub offs: HashMap<&'ctx str, HashMap<&'ctx str, Vec<Bool<'ctx>>>>,
    pub semantics: Semantics,
}

impl<'env, 'ctx> AHLTLObject<'env, 'ctx> {
    pub fn new(
        envs: &'env Vec<SMVEnv<'ctx>>,
        formula: &'ctx AstNode,
        paths: Vec<&'ctx str>, 
        trajs: Vec<&'ctx str>,
        path_mappings: HashMap<&'ctx str, usize>,
        positions: HashMap<&'ctx str, HashMap<&'ctx str, HashMap<String, Bool<'ctx>>>>,
        trajectories: HashMap<&'ctx str, HashMap<&'ctx str, Vec<Bool<'ctx>>>>,
        offs: HashMap<&'ctx str, HashMap<&'ctx str, Vec<Bool<'ctx>>>>,
        k: usize,
        m: usize,
        semantics: Semantics,
    ) -> Self {
        //Generate the corresponding states and path encoding for each name
        let mut states: Vec<Vec<EnvState<'ctx>>> = Vec::new();
        for (idx, &name) in paths.iter().enumerate() {
            let (new_states, _) = envs[idx].generate_symbolic_path(k, Some(name));
            states.push(new_states);
        }
        AHLTLObject {
            envs,
            states,
            formula,
            k,
            m,
            paths,
            trajs,
            path_mappings,
            positions,
            trajectories,
            offs,
            semantics,
        }
    }

    pub fn flatten_pos(& self) -> Vec<&Bool<'ctx>> {
        self.positions
        .values()
        .flat_map(|path_map| path_map.values())
        .flat_map(|ij_map| ij_map.values())
        .collect()
    }
    pub fn flatten_traj(& self) -> HashMap<&'ctx str, Vec<&Bool<'ctx>>> {
        let mut hash_out = HashMap::with_capacity(self.trajectories.len());
        for (&traj_key, path_map) in &self.trajectories {
            let mut flat = Vec::new();
            for vec_bool in path_map.values() {
                flat.extend(vec_bool.iter());
            }
            hash_out.insert(traj_key, flat);
        }
        hash_out
    }
    pub fn flatten_off(& self) -> Vec<&Bool<'ctx>> {
        self.offs
        .values()
        .flat_map(|path_map| path_map.values())
        .flat_map(|v| v.iter())
        .collect()
    }

    fn setpos(& self, path_name: &str, traj_name: &str, i: usize, j: usize) -> Bool<'ctx> {
        let idx = format!("{}_{}", i, j);
        let pos = &self.positions[traj_name][path_name][&idx];
        let mut constraints = vec![pos.clone()];
        for n in 0..=self.k {
            if n != i {
                let curr_idx = format!("{}_{}", n, j);
                let node = &self.positions[traj_name][path_name][&curr_idx];
                constraints.push(
                    node.clone().not()
                );
            }
        }
        let off_node = &self.offs[traj_name][path_name][j];
        constraints.push(off_node.clone().not());
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::and(self.envs[0].ctx, &refs)
    }

    fn nopos(& self, path_name: &str, traj_name: &str, j: usize) -> Bool<'ctx> {
        let off = &self.offs[traj_name][path_name][j];
        let mut constraints = vec![off.clone()];
        for n in 0..=self.k {
            let curr_idx = format!("{}_{}", n, j);
            let node = &self.positions[traj_name][path_name][&curr_idx];
            constraints.push(
                node.clone().not()
            );
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::and(self.envs[0].ctx, &refs)
    }

    fn init_pos(& self) -> Bool<'ctx> {
        let mut constraints: Vec<Bool<'ctx>> = Vec::new();

        for traj in &self.trajs {
            for path in &self.paths {
                constraints.push(self.setpos(path, traj, 0, 0));
            }
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::and(self.envs[0].ctx, &refs)
    }

    fn step(& self, path_name: &str, traj_name: &str, j: usize) -> Bool<'ctx> {
        let mut constraints = Vec::with_capacity(self.k);
        for i in 0..self.k {
            let ij_key = format!("{}_{}", i, j);
            let pos = &self.positions[traj_name][path_name][&ij_key];
            let trj = &self.trajectories[traj_name][path_name][j];
            let lhs = pos & trj;
            constraints.push(
                Bool::implies(
                    &lhs,
                    &self.setpos(path_name, traj_name, i + 1, j + 1)
                )
            );
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::and(self.envs[0].ctx, &refs)
    }

    fn stutters(& self, path_name: &str, traj_name: &str, j: usize) -> Bool<'ctx> {
        let mut constraints = Vec::with_capacity(self.k + 1);
        for i in 0..=self.k {
            let ij_key = format!("{}_{}", i, j);
            let pos = &self.positions[traj_name][path_name][&ij_key];
            let trj = &self.trajectories[traj_name][path_name][j].not();
            let lhs = pos & trj;
            constraints.push(
                Bool::implies(
                    &lhs,
                    &self.setpos(path_name, traj_name, i, j + 1)
                )
            );
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::and(self.envs[0].ctx, &refs)
    }

    fn ends(& self, path_name: &str, traj_name: &str, j: usize) -> Bool<'ctx> {
        let ij_key = format!("{}_{}", self.k, j);
        let pos = &self.positions[traj_name][path_name][&ij_key];
        let trj = &self.trajectories[traj_name][path_name][j];
        let lhs = pos & trj;
        // get the index of the corresponding state variables
        let path_idx = self.path_mappings[path_name];
        let kth_state = &self.states[path_idx][self.k];
        let halt_k = self.envs[path_idx].predicates["halt"](&self.envs[path_idx], self.envs[0].ctx, &kth_state);
        let left_of_rhs = Bool::implies(
            &halt_k.not(),
            &self.nopos(path_name, traj_name, j + 1)
        );
        let right_of_rhs = Bool::implies(
            &halt_k,
            &self.setpos(path_name, traj_name, self.k, j + 1)
        );
        let rhs = left_of_rhs & right_of_rhs;
        Bool::implies(&lhs, &rhs)
    }

    fn pos(& self) -> Bool<'ctx> {
        let mut constraints = vec![self.init_pos()];
        for j in 0..self.m {
            for &traj_name in &self.trajs {
                for &path_name in &self.paths {
                    constraints.push(
                        self.step(path_name, traj_name, j) &
                        self.stutters(path_name, traj_name, j) &
                        self.ends(path_name, traj_name, j)
                    );
                }
            }
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::and(self.envs[0].ctx, &refs)
    }

    fn off_disj(& self, j: usize) -> Bool<'ctx> {
        let mut constraints: Vec<Bool> = Vec::new();
        for &traj_name in &self.trajs {
            for &path_name in &self.paths {
                let node = &self.offs[traj_name][path_name][j];
                constraints.push(node.clone());
            }
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::or(self.envs[0].ctx, &refs)
    }

    fn halt_pi_tau(& self, path_name: &str, traj_name: &str, i: usize, j: usize) -> Bool<'ctx> {
        let path_idx = self.path_mappings[path_name];
        let ith_state = &self.states[path_idx][i];
        let halt = self.envs[path_idx].predicates["halt"](&self.envs[path_idx], self.envs[0].ctx, &ith_state);
        let ij_key = format!("{}_{}", i, j);
        let pos = &self.positions[traj_name][path_name][&ij_key];
        pos & halt
    }

    fn not_halt_pi_tau(& self, path_name: &str, traj_name: &str, i: usize, j: usize) -> Bool<'ctx> {
        let path_idx = self.path_mappings[path_name];
        let ith_state = &self.states[path_idx][i];
        let halt = self.envs[path_idx].predicates["halt"](&self.envs[path_idx], self.envs[0].ctx, &ith_state);
        let ij_key = format!("{}_{}", i, j);
        let pos = &self.positions[traj_name][path_name][&ij_key];
        pos & halt.not()

    }

    fn halt_pi_tau_disj(& self, path_name: &str, traj_name: &str, j: usize) -> Bool<'ctx> {
        let mut constraints = Vec::with_capacity(self.k + 1);
        for i in 0..=self.k {
            constraints.push(self.halt_pi_tau(path_name, traj_name, i, j));
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::or(self.envs[0].ctx, &refs)
    }

    fn not_halt_pi_tau_disj(& self, path_name: &str, traj_name: &str, j: usize) -> Bool<'ctx> {
        let mut constraints = Vec::with_capacity(self.k + 1);
        for i in 0..=self.k {
            constraints.push(self.not_halt_pi_tau(path_name, traj_name, i, j));
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::or(self.envs[0].ctx, &refs)
    }

    fn halted_traj(& self, traj_name: &str, j: usize) -> Bool<'ctx> {
        let mut constraints = Vec::with_capacity(self.paths.len());
        for &path_name in &self.paths {
            constraints.push(self.halt_pi_tau_disj(path_name, traj_name, j));
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::and(self.envs[0].ctx, &refs)
    }

    fn halted(& self, j: usize, trajs: Option<&Vec<&'ctx str>>) -> Bool<'ctx> {
        let trajs = match trajs {
            None => &self.trajs,
            Some(t) => t
        };
        let mut constraints = Vec::with_capacity(trajs.len());
        for &traj_name in trajs {
            constraints.push(self.halted_traj(traj_name, j));
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::and(self.envs[0].ctx, &refs)
    }

    fn moves(& self, j: usize, trajs: Option<&Vec<&'ctx str>>) -> Bool<'ctx> {
        let mut rhs_constraints = Vec::new();
        let lhs = self.halted(j, trajs);
        
        let trajs = match trajs {
            None => &self.trajs,
            Some(t) => t
        };
        
        for &traj_name in trajs {
            for &path_name in &self.paths {
                rhs_constraints.push(
                    &self.trajectories[traj_name][path_name][j] &
                    self.not_halt_pi_tau_disj(path_name, traj_name, j)
                );
            }
        }
        let refs: Vec<&Bool> = rhs_constraints.iter().collect();
        let rhs = Bool::or(self.envs[0].ctx, &refs);
        lhs | rhs
    }

    fn enc(& self) -> Bool<'ctx> {
        // First, get the inner-ltl formula
        let inner = inner_ltl(self.formula);

        // Structure-based construction of the inner encoding
        if is_E(self.formula) {
            let mut lhs_constraints = Vec::with_capacity(self.m + 1);
            for j in 0..=self.m {
                lhs_constraints.push(self.moves(j, None));
            }
            let refs: Vec<&Bool> = lhs_constraints.iter().collect();
            let lhs = Bool::and(self.envs[0].ctx, &refs);
            return lhs & self.shared_semantics(inner, 0);
        
        }else if is_A(self.formula) {
            let mut lhs_constraints = Vec::with_capacity(self.m + 1);
            for j in 0..=self.m {
                lhs_constraints.push(self.moves(j, None));
            }
            let refs: Vec<&Bool> = lhs_constraints.iter().collect();
            let lhs = Bool::and(self.envs[0].ctx, &refs);
            return Bool::implies(&lhs, &self.shared_semantics(inner, 0));
        
        }else if is_AE(self.formula) {
            let trajs_A = get_forall_trajs(self.formula);
            let trajs_E = get_exists_trajs(self.formula);
            
            let mut lhs_const = Vec::with_capacity(self.m + 1);
            for j in 0..=self.m {
                lhs_const.push(self.moves(j, Some(&trajs_A)));
            }
            let lhs_refs: Vec<&Bool> = lhs_const.iter().collect();
            let lhs = Bool::and(self.envs[0].ctx, &lhs_refs);

            let mut rhs_const = Vec::with_capacity(self.m + 2);
            for j in 0..=self.m {
                rhs_const.push(
                    Bool::implies(
                        &self.halted(j, Some(&trajs_A)),
                        &self.moves(j, Some(&trajs_E))
                    )
                );
            }
            rhs_const.push(self.shared_semantics(inner, 0));
            let rhs_refs: Vec<&Bool> = rhs_const.iter().collect();
            let rhs = Bool::and(self.envs[0].ctx, &rhs_refs);
            Bool::implies(&lhs, &rhs)
            
        }else if is_EA(self.formula) {
            let trajs_A = get_forall_trajs(self.formula);
            let trajs_E = get_exists_trajs(self.formula);
            
            let mut lhs_const = Vec::with_capacity(self.m + 1);
            for j in 0..=self.m {
                lhs_const.push(self.moves(j, Some(&trajs_E)));
            }
            let lhs_refs: Vec<&Bool> = lhs_const.iter().collect();
            let lhs = Bool::and(self.envs[0].ctx, &lhs_refs);

            let mut rhs_const = Vec::with_capacity(self.m + 1);
            for j in 0..=self.m {
                rhs_const.push(
                    Bool::implies(
                        &self.halted(j, Some(&trajs_E)),
                        &self.moves(j, Some(&trajs_A))
                    )
                );
            }
            let rhs_refs: Vec<&Bool> = rhs_const.iter().collect();
            let rhs_imp = Bool::and(self.envs[0].ctx, &rhs_refs);
            let rhs = Bool::implies(&rhs_imp, &self.shared_semantics(inner, 0));
            lhs & rhs

        }else {
            panic!("Invalid trajectory quantifier types. Check you formula.");
        }
    }

    pub fn build_inner(& self) -> Bool<'ctx> {
        self.pos() & self.enc()
    }

    fn shared_semantics(& self, formula: &AstNode, j: usize) -> Bool<'ctx> {
        match formula {
            AstNode::Constant {value} => {
                if value == "TRUE" {
                    Bool::from_bool(self.envs[0].ctx, true)
                }else if value == "FALSE" {
                    Bool::from_bool(self.envs[0].ctx, false)
                }else {
                    panic!("Only Boolean constants are supported in AHLTL mode.")
                }
            }
            AstNode::AIndexedProp {proposition, path_identifier, traj_identifier} => {
                let mut constraints = Vec::with_capacity(self.k + 1);
                let path_idx = self.path_mappings[path_identifier.as_str()];
                for i in 0..=self.k {
                    let ith_state = &self.states[path_idx][i]; // Containts all variables
                    let proposition = match ith_state.get(proposition as &str) {
                        Some(v) => v.as_bool().unwrap(), // variable exists
                        None => {
                            // Might be a predicate
                            let env = &self.envs[path_idx];
                            match env.predicates.get(proposition as &str) {
                                Some(predicate) => {
                                    // Apply the predicate and return
                                    predicate(&env, env.ctx, &ith_state)
                                }
                                None => panic!("Udnefined variable or predicate `{}`", proposition)
                            }
                        }
                    };
                    let ij_key = format!("{}_{}", i, j);
                    constraints.push(
                        &self.positions[traj_identifier.as_str()][path_identifier.as_str()][&ij_key] &
                        proposition
                    );
                }
                let refs: Vec<&Bool> = constraints.iter().collect();
                Bool::or(self.envs[0].ctx, &refs)
            }
            AstNode::UnOp {operator, operand} => {
                match operator {
                    UnaryOperator::Negation => {
                        // Check whether the operand is an identifier
                        match &**operand {
                            AstNode::AIndexedProp {proposition, path_identifier, traj_identifier} => {
                                let mut constraints = Vec::with_capacity(self.k + 1);
                                let path_idx = self.path_mappings[path_identifier.as_str()];
                                for i in 0..=self.k {
                                    let ith_state = &self.states[path_idx][i]; // Containts all variables
                                    let proposition = match ith_state.get(proposition as &str) {
                                        Some(v) => v.as_bool().unwrap(), // variable exists
                                        None => {
                                            // Might be a predicate
                                            let env = &self.envs[path_idx];
                                            match env.predicates.get(proposition as &str) {
                                                Some(predicate) => {
                                                    // Apply the predicate and return
                                                    predicate(&env, env.ctx, &ith_state)
                                                }
                                                None => panic!("Udnefined variable or predicate `{}`", proposition)
                                            }
                                        }
                                    };
                                    let ij_key = format!("{}_{}", i, j);
                                    constraints.push(
                                        &self.positions[traj_identifier.as_str()][path_identifier.as_str()][&ij_key] &
                                        proposition.not()
                                    );
                                }
                                let refs: Vec<&Bool> = constraints.iter().collect();
                                Bool::or(self.envs[0].ctx, &refs)
                            }
                            _ => self.shared_semantics(operand, j).not()
                        }
                    }
                    UnaryOperator::Globally => {
                        // Create a new formula: FALSE R operand
                        let false_boxed = Box::new(
                            AstNode::Constant{value: String::from("FALSE")}
                        );
                        let release_equiv = Box::new(AstNode::BinOp{
                            operator: BinOperator::Release,
                            lhs: false_boxed,
                            rhs: operand.clone(),
                        });
                        self.shared_semantics(&release_equiv, j)
                    }
                    UnaryOperator::Eventually => {
                        // Create a new formula: TRUE U operand
                        let true_boxed = Box::new(
                            AstNode::Constant{value: String::from("TRUE")}
                        );
                        let until_equiv = Box::new(AstNode::BinOp{
                            operator: BinOperator::Until,
                            lhs: true_boxed,
                            rhs: operand.clone(),
                        });
                        self.shared_semantics(&until_equiv, j)
                    }
                    _ => unreachable!(),
                }
            }
            AstNode::BinOp {operator, lhs, rhs} => {
                match operator {
                    // TODO: Variable
                    BinOperator::Equality => {
                        let lhs_bool = self.shared_semantics(lhs, j);
                        let rhs_bool = self.shared_semantics(rhs, j);
                        let pos = lhs_bool.clone() & rhs_bool.clone();
                        // Also need to consider the negation
                        let lhs_negated_node = Box::new(AstNode::UnOp {
                            operator: UnaryOperator::Negation,
                            operand: lhs.clone(),
                        });
                        let lhs_neg_bool = self.shared_semantics(&lhs_negated_node, j);
                        let rhs_negated_node = Box::new(AstNode::UnOp {
                            operator: UnaryOperator::Negation,
                            operand: rhs.clone(),
                        });
                        let rhs_neg_bool = self.shared_semantics(&rhs_negated_node, j);
                        let neg = lhs_neg_bool.clone() & rhs_neg_bool.clone();
                        pos | neg
                    }
                    BinOperator::Conjunction => {
                        let lhs_bool = self.shared_semantics(lhs, j);
                        let rhs_bool = self.shared_semantics(rhs, j);
                        lhs_bool & rhs_bool
                    }
                    BinOperator::Disjunction => {
                        let lhs_bool = self.shared_semantics(lhs, j);
                        let rhs_bool = self.shared_semantics(rhs, j);
                        lhs_bool | rhs_bool
                    }
                    BinOperator::Implication => {
                        let lhs_bool = self.shared_semantics(lhs, j);
                        let rhs_bool = self.shared_semantics(rhs, j);
                        Bool::implies(&lhs_bool, &rhs_bool)
                    }
                    BinOperator::Until |
                    BinOperator::Release => {
                        match self.semantics {
                            Semantics::Hpes => self.semantics_hpes(formula, j),
                            Semantics::Hopt => self.semantics_hopt(formula, j),
                            _ => unreachable!(),
                        }
                    }
                }
            }
            _ => todo!(),
        }
    }

    fn semantics_hpes(& self, formula: &AstNode, j: usize) -> Bool<'ctx> {
        // We already know the structure of the current formula: U or R
        match formula {
            AstNode::BinOp {operator, lhs, rhs} => {
                match operator {
                    BinOperator::Until => {
                        // Check the value of j
                        if j < self.m {
                            let lhs_bool = self.shared_semantics(lhs, j);
                            let rhs_bool = self.shared_semantics(rhs, j);
                            let rec_unrolling = rhs_bool | (lhs_bool & self.shared_semantics(formula, j + 1));
                            self.off_disj(j).not() & rec_unrolling
                        }else if j == self.m {
                            self.shared_semantics(lhs, j)
                        }else {
                            panic!("Invalid `j` value in hpes (Until)");
                        }
                    }
                    BinOperator::Release => {
                        // Check the value of j
                        if j < self.m {
                            let lhs_bool = self.shared_semantics(lhs, j);
                            let rhs_bool = self.shared_semantics(rhs, j);
                            let rec_unrolling = rhs_bool & (lhs_bool | self.shared_semantics(formula, j + 1));
                            self.off_disj(j).not() & rec_unrolling
                        }else if j == self.m {
                            let lhs = self.shared_semantics(lhs, j) & self.shared_semantics(rhs, j);
                            let rhs = self.halted(j, None) & self.shared_semantics(rhs, j);
                            lhs | rhs
                        }else {
                            panic!("Invalid `j` value in hpes (Release)");
                        }
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
    }
    
    fn semantics_hopt(& self, formula: &AstNode, j: usize) -> Bool<'ctx> {
        // We already know the structure of the current formula: U or R
        match formula {
            AstNode::BinOp {operator, lhs, rhs} => {
                match operator {
                    BinOperator::Until => {
                        // Check the value of j
                        if j < self.m {
                            let lhs_bool = self.shared_semantics(lhs, j);
                            let rhs_bool = self.shared_semantics(rhs, j);
                            let rec_unrolling = rhs_bool | (lhs_bool & self.shared_semantics(formula, j + 1));
                            self.off_disj(j) | rec_unrolling
                        }else if j == self.m {
                            self.shared_semantics(rhs, j) | (self.halted(j, None) & self.shared_semantics(lhs, j))
                        }else {
                            panic!("Invalid `j` value in hopt (Until)");
                        }
                    }
                    BinOperator::Release => {
                        if j < self.m {
                            let lhs_bool = self.shared_semantics(lhs, j);
                            let rhs_bool = self.shared_semantics(rhs, j);
                            let rec_unrolling = rhs_bool & (lhs_bool | self.shared_semantics(formula, j + 1));
                            self.off_disj(j) | rec_unrolling
                        }else if j == self.m {
                            self.shared_semantics(rhs, j)
                        }else {
                            panic!("Invalid `j` value in hopt (Release)");
                        }
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
    }
}