use ir::*;
use z3::Context;
use z3::ast::{Ast, Int, Bool, Dynamic};
use llvm_ir::Module;
use indexmap::IndexMap;
use crate::llvm_analyzer;

pub fn create_ts_from_c<'ctx>(
    ctx: &'ctx Context,
    vars: &'ctx IndexMap<String, llvm_analyzer::VarRef>,
    transitions: &'ctx Vec<llvm_analyzer::VarTransition>,
    num_instr: usize,
) -> SMVEnv<'ctx> {
    // Collect variables
    let mut env = SMVEnv::new(ctx);
    register_variables(&mut env, vars);
    // Register PC at the end
    env.register_variable(
        "%__pc",
        VarType::Int {
            init: Some(vec![0]),
            lower: Some(0),
            upper: Some((num_instr - 1) as i64)});
    register_transitions(&mut env, transitions);
    // Register the self-loop for PC
    env.register_transition(
        "%__pc",
        move |_env, ctx, state: &EnvState| {
            let pc_done: i64 = (num_instr - 1) as i64;
            let done_node = Int::from_i64(ctx, pc_done);
            let eq_node = int_var!(state, "%__pc")._eq(&done_node);
            ReturnType::DynAst(to_dyn!(eq_node))
        },
        move |_env, _ctx, state: &EnvState| ReturnType::DynAst(to_dyn!(int_var!(state, "%__pc")))
    );
    // Register increment
    env.register_transition(
        "%__pc",
        move |_env, _ctx, _state: &EnvState| ReturnType::Bool(vec![true]),
        move |_env, ctx, state: &EnvState| {
            let one = Int::from_i64(ctx, 1i64);
            let inc_node = int_var!(state, "%__pc") + one;
            ReturnType::DynAst(to_dyn!(inc_node))
        },
    );
    env
}

fn register_variables<'ctx>(env: &mut SMVEnv<'ctx>, vars: &'ctx IndexMap<String, llvm_analyzer::VarRef>) {
    for (name, var_ref) in vars.iter() {
        // Create the Sort
        let var_sort = match var_ref.type_ref {
            llvm_analyzer::TypeRef::IntegerType(_) => {
                // transform initial from Option<u64> to Option<Vec<i64>>
                // Only works if there is a single element in the initital
                let init = var_ref.initial.map(|v| vec![v as i64]);
                VarType::Int {
                    init,
                    lower: None,
                    upper: None,
                }
            }
            llvm_analyzer::TypeRef::BoolType(_) => {
                VarType::Bool {init: None}
            }
        };
        env.register_variable(name.as_str(), var_sort);
    }
}

fn register_transitions<'ctx>(env: &mut SMVEnv<'ctx>, transitions: &'ctx Vec<llvm_analyzer::VarTransition>) {
    for transition in transitions {
        let curr_pc: i64 = transition.from_pc as i64;
        if transition.cond.is_none() {
            // If the condition is not set, it is not pc
            let guard_fn = move |_env: &SMVEnv<'ctx>, ctx: &'ctx Context, state: &EnvState<'ctx>| {
                let curr_pc_node = Int::from_i64(ctx, curr_pc);
                ReturnType::DynAst(to_dyn!(int_var!(state, "%__pc")._eq(&curr_pc_node)))
            };

            match &transition.upd {
                llvm_analyzer::UpdateType::ConstantUpdate(v) => {
                    let update_value: i64 = *v as i64;
                    env.register_transition(
                        transition.var.as_str(),
                        guard_fn,
                        move |_env, _ctx, _state: &EnvState| ReturnType::Int(vec![update_value]),
                    );
                }
                llvm_analyzer::UpdateType::VariableUpdate(name) => {
                    let name_cl = name.clone();
                    env.register_transition(
                        transition.var.as_str(),
                        guard_fn,
                        move |_env, _ctx, state: &EnvState| {
                            ReturnType::DynAst(to_dyn!(int_var!(state, name_cl.as_str())))
                        },
                    );
                }
                llvm_analyzer::UpdateType::ComparisonUpdate { operator, lhs, rhs } => {
                    let lhs_cl = lhs.clone();
                    let rhs_cl = rhs.clone();

                    match operator.as_str() {
                        "EQ" => {
                            env.register_transition(
                                transition.var.as_str(),
                                guard_fn,
                                move |_env, _ctx, state: &EnvState| {
                                    let l = int_var!(state, lhs_cl.as_str());
                                    let r = int_var!(state, rhs_cl.as_str());
                                    ReturnType::DynAst(to_dyn!(l._eq(&r)))
                                },
                            );
                        }
                        "NE" => {
                            env.register_transition(
                                transition.var.as_str(),
                                guard_fn,
                                move |_env, _ctx, state: &EnvState| {
                                    let l = int_var!(state, lhs_cl.as_str());
                                    let r = int_var!(state, rhs_cl.as_str());
                                    ReturnType::DynAst(to_dyn!(l._eq(&r).not()))
                                },
                            );
                        }
                        _ => {
                            panic!("Conditional operator not implemented in the parser");
                        }
                    }
                }
            }

        }else {
            // It is a PC transition
            let (var_name, condition) = transition.cond.clone().unwrap();
            match condition {
                true => {
                    let guard_fn = move |_env: &SMVEnv<'ctx>, ctx: &'ctx Context, state: &EnvState<'ctx>| {
                        let curr_pc_node = Int::from_i64(ctx, curr_pc);
                        let is_pc_curr = int_var!(state, "%__pc")._eq(&curr_pc_node);
                        let cond_node = bool_var!(state, var_name.as_str());
                        let conj_node = is_pc_curr & cond_node;
                        ReturnType::DynAst(to_dyn!(conj_node))
                    };
                    //update is a Constant value, also achieveable from to_pc
                    let next_pc: i64 = transition.to_pc as i64;
                    env.register_transition(
                        "%__pc",
                        guard_fn,
                        move |_env, _ctx, _state: &EnvState| ReturnType::Int(vec![next_pc])
                    );
                }
                false => {
                    let guard_fn = move |_env: &SMVEnv<'ctx>, ctx: &'ctx Context, state: &EnvState<'ctx>| {
                        let curr_pc_node = Int::from_i64(ctx, curr_pc);
                        let is_pc_curr = int_var!(state, "%__pc")._eq(&curr_pc_node);
                        let cond_node = bool_var!(state, var_name.as_str()).not();
                        let conj_node = is_pc_curr & cond_node;
                        ReturnType::DynAst(to_dyn!(conj_node))
                    };
                    //update is a Constant value, also achieveable from to_pc
                    let next_pc: i64 = transition.to_pc as i64;
                    env.register_transition(
                        "%__pc",
                        guard_fn,
                        move |_env, _ctx, _state: &EnvState| ReturnType::Int(vec![next_pc])
                    );
                }
            }

        }
    }
}