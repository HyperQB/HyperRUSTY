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
    pub env: &'env SMVEnv<'ctx>,
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
        env: &'env SMVEnv<'ctx>,
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
        for &name in &paths {
            let (new_states, _) = env.generate_symbolic_path(k, Some(name));
            states.push(new_states);
        }
        AHLTLObject {
            env,
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
        Bool::and(self.env.ctx, &refs)
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
        Bool::and(self.env.ctx, &refs)
    }

    fn init_pos(& self) -> Bool<'ctx> {
        let mut constraints: Vec<Bool<'ctx>> = Vec::new();

        for traj in &self.trajs {
            for path in &self.paths {
                constraints.push(self.setpos(path, traj, 0, 0));
            }
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::and(self.env.ctx, &refs)
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
        Bool::and(self.env.ctx, &refs)
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
        Bool::and(self.env.ctx, &refs)
    }

    fn ends(& self, path_name: &str, traj_name: &str, j: usize) -> Bool<'ctx> {
        let ij_key = format!("{}_{}", self.k, j);
        let pos = &self.positions[traj_name][path_name][&ij_key];
        let trj = &self.trajectories[traj_name][path_name][j];
        let lhs = pos & trj;
        // get the index of the corresponding state variables
        let path_idx = self.path_mappings[path_name];
        let kth_state = &self.states[path_idx][self.k];
        let halt_k = self.env.predicates["halt"](self.env, self.env.ctx, &kth_state);
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
        Bool::and(self.env.ctx, &refs)
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
        Bool::or(self.env.ctx, &refs)
    }

    fn halt_pi_tau(& self, path_name: &str, traj_name: &str, i: usize, j: usize) -> Bool<'ctx> {
        let path_idx = self.path_mappings[path_name];
        let ith_state = &self.states[path_idx][i];
        let halt = self.env.predicates["halt"](self.env, self.env.ctx, &ith_state);
        let ij_key = format!("{}_{}", i, j);
        let pos = &self.positions[traj_name][path_name][&ij_key];
        pos & halt
    }

    fn not_halt_pi_tau(& self, path_name: &str, traj_name: &str, i: usize, j: usize) -> Bool<'ctx> {
        let path_idx = self.path_mappings[path_name];
        let ith_state = &self.states[path_idx][i];
        let halt = self.env.predicates["halt"](self.env, self.env.ctx, &ith_state);
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
        Bool::or(self.env.ctx, &refs)
    }

    fn not_halt_pi_tau_disj(& self, path_name: &str, traj_name: &str, j: usize) -> Bool<'ctx> {
        let mut constraints = Vec::with_capacity(self.k + 1);
        for i in 0..=self.k {
            constraints.push(self.not_halt_pi_tau(path_name, traj_name, i, j));
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::or(self.env.ctx, &refs)
    }

    fn halted_traj(& self, traj_name: &str, j: usize) -> Bool<'ctx> {
        let mut constraints = Vec::with_capacity(self.paths.len());
        for &path_name in &self.paths {
            constraints.push(self.halt_pi_tau_disj(path_name, traj_name, j));
        }
        let refs: Vec<&Bool> = constraints.iter().collect();
        Bool::and(self.env.ctx, &refs)
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
        Bool::and(self.env.ctx, &refs)
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
        let rhs = Bool::or(self.env.ctx, &refs);
        lhs | rhs
    }

    // fn shared_semantics(& self, form: &AstNode, j: usize) -> Bool<'ctx> {
    //     match formula {

    //     }
    // }



}