use z3::{
    ast::{
        Ast, Bool, Dynamic, 
        forall_const, exists_const,
    },
    Context, Model,
};
use std::collections::{HashMap, HashSet};
use std::ffi::{CString, CStr};
use indexmap::IndexMap;
use ahltlunroller::*;
use hltlunroller::*;
use regex::Regex;
use enchelper::*;
use parser::*;
use z3_sys::*;
use std::ptr;
use ir::*;

mod verilog_helper;

/****************************
*
*   Shared Encoding functions
*
****************************/

pub fn get_z3_encoding<'env, 'ctx>(envs: &'env Vec<SMVEnv<'ctx>>, formula: &'ctx AstNode, k: usize, m: Option<usize>, sem: Semantics, witness: bool) -> Bool<'env> {
    // First, extract path names from the formula
    let path_names = get_path_identifiers(formula);
    // Next, get the corresponding states and path encoding for each name
    let mut states: Vec<Vec<EnvState<'ctx>>> = Vec::new();
    let mut constraints: Vec<Bool<'env>> = Vec::new();
    for (idx, &name) in path_names.iter().enumerate() {
        let (new_states, new_constraint) = envs[idx].generate_symbolic_path(k, Some(name));
        states.push(new_states);
        constraints.push(new_constraint);
    }

    // detect the type of formula
    if is_hltl(formula) {
        // Last, call the encoding generator
        generate_hltl_encoding(envs, formula, states, constraints, sem, witness)
    }else {
        // It's an A-HLTL formula
        // Extract M. If it is not provided, panic!
        let m = match m {
            Some(m) => m,
            None => panic!("Unrolling bound of trajectories can not be None!"),
        };
        // The semantics must be halting
        if !matches!(sem, Semantics::Hpes | Semantics::Hopt) {
            panic!("Only halting semantics are allowed for A-HLTL BMC.");
        }
        // Call the AHLTL encoding generator
        generate_ahltl_encoding(envs, formula, states, constraints, m, sem, witness)
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

/****************************
*
*   AHLTL Encoding Functions
*
****************************/

fn generate_ahltl_encoding<'env, 'ctx>(envs: &'env Vec<SMVEnv<'ctx>>, formula: &'ctx AstNode, states: Vec<Vec<EnvState<'ctx>>>, constraints: Vec<Bool<'env>>, m: usize, sem: Semantics, witness: bool) -> Bool<'env> {
    let k: usize = states[0].len() - 1;
    let path_names = get_path_identifiers(formula);

    // First, create path mappings
    let mapping = create_path_mapping(formula, 0);
    // Second, get trajectory names
    let traj_names = get_traj_identifiers(formula);
    // Next, create position, trajectory, and off encoding variables
    let mut positions = HashMap::new();
    for traj in &traj_names {
        let mut path_map = HashMap::new();
        for path in &path_names {
            let mut ij_map = HashMap::new();
            for i in 0..=k {
                for j in 0..=m {
                    let key = format!("{}_{}", i, j);
                    let val = Bool::new_const(
                        envs[0].ctx,
                        format!("pos_{}_{}_{}_{}", path, traj, i, j),
                    );
                    ij_map.insert(key, val);
                }
            }
            path_map.insert(path.clone(), ij_map);
        }
        positions.insert(traj.clone(), path_map);
    }
    
    let mut trajectories = HashMap::new();
    for traj in &traj_names {
        let traj_key = traj.clone();
        let mut path_map = HashMap::new();
        for path in &path_names {
            let path_key = path.clone();
            let mut bool_vec = Vec::with_capacity(m + 1);
            for j in 0..=m {
                let name = format!("{}_{}_{}", traj, path, j);
                let b = Bool::new_const(envs[0].ctx, name);
                bool_vec.push(b);
            }
            path_map.insert(path_key, bool_vec);
        }
        trajectories.insert(traj_key, path_map);
    }

    let mut off = HashMap::new();
    for traj in &traj_names {
        let traj_key = traj.clone();
        let mut path_map = HashMap::new();
        for path in &path_names {
            let path_key = path.clone();
            let mut bool_vec = Vec::with_capacity(m + 1);
            for j in 0..=m {
                let name = format!("off_{}_{}_{}", path, traj, j);
                let b = Bool::new_const(envs[0].ctx, name);
                bool_vec.push(b);
            }
            path_map.insert(path_key, bool_vec);
        }
        off.insert(traj_key, path_map);
    }

    let ahltl_obj = AHLTLObject::new(
        envs,
        &states,
        formula,
        path_names.clone(),
        traj_names,
        mapping,
        positions,
        trajectories,
        off,
        k,
        m,
        sem,
    );
    // Generate the mapping again (why?)
    let mapping = create_path_mapping(formula, 0);

    // Get the A-HLTL pos /\ enc(phi) encoding
    let inner_ltl = ahltl_obj.build_inner();
    // Include valid path conditions
    let inner_with_paths = generate_inner_encoding(envs[0].ctx, formula, &constraints, inner_ltl, 0);

    // Create a partial encoding for E pos. E off. inner_with_paths
    let flat_pos: Vec<_> = ahltl_obj.flatten_pos();
    let pos_refs: Vec<&dyn Ast<'env>> = flat_pos.iter().map(|v| *v as &dyn Ast<'env>).collect();
    let flat_off: Vec<_> = ahltl_obj.flatten_off();
    let off_refs: Vec<&dyn Ast<'env>> = flat_off.iter().map(|v| *v as &dyn Ast<'env>).collect();
    let partial_formula = exists_const(
        envs[0].ctx,
        &pos_refs,
        &[],
        &exists_const(
            envs[0].ctx,
            &off_refs,
            &[],
            &inner_with_paths,
        ),
    );
    let flat_traj = ahltl_obj.flatten_traj();
    // If the witness flag is set, strip all leading existentials
    if witness {
        complete_ahltl_encoding(envs[0].ctx, strip_leading_existentials(formula), partial_formula, flat_traj, &states, &mapping)
    }else {
        complete_ahltl_encoding(envs[0].ctx, formula, partial_formula, flat_traj, &states, &mapping)
    }
}

pub fn complete_ahltl_encoding<'ctx>(ctx: &'ctx Context, formula: &AstNode, inner: Bool<'ctx>, traj: HashMap<&'ctx str, Vec<&Bool<'ctx>>>, states: &Vec<Vec<EnvState<'ctx>>>, mapping: &HashMap<&str, usize>) -> Bool<'ctx> {
    match formula {
        AstNode::HAQuantifier {identifier, form} => {
            let idx = mapping[identifier as &str];
            let selected_path = &states[idx];
            let vars: Vec<Dynamic<'ctx>> = selected_path
                .iter()
                .flat_map(|env| env.values().cloned()) // clones Dynamic<'ctx>
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            forall_const(
                ctx,
                &ast_refs,
                &[],
                &complete_ahltl_encoding(ctx, form, inner, traj, states, mapping)
            )
        }
        AstNode::HEQuantifier {identifier, form} => {
            let idx = mapping[identifier as &str];
            let selected_path = &states[idx];
            let vars: Vec<Dynamic<'ctx>> = selected_path
                .iter()
                .flat_map(|env| env.values().cloned()) // clones Dynamic<'ctx>
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            exists_const(
                ctx,
                &ast_refs,
                &[],
                &complete_ahltl_encoding(ctx, form, inner, traj, states, mapping)
            )
        }
        AstNode::AEQuantifier {identifier, form} => {
            // Get the corresponding variables from trajectories
            let selected_vars = &traj[identifier as &str];
            let vars: Vec<Dynamic<'ctx>> = selected_vars
                .iter()
                .copied()
                .map(|node| Dynamic::from_ast(node))
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            exists_const(
                ctx,
                &ast_refs,
                &[],
                &complete_ahltl_encoding(ctx, form, inner, traj, states, mapping)
            )
        }
        AstNode::AAQuantifier {identifier, form} => {
            // Get the corresponding variables from trajectories
            let selected_vars = &traj[identifier as &str];
            let vars: Vec<Dynamic<'ctx>> = selected_vars
                .iter()
                .copied()
                .map(|node| Dynamic::from_ast(node))
                .collect();
            let ast_refs: Vec<&dyn Ast<'ctx>> = vars.iter().map(|v| v as &dyn Ast<'ctx>).collect();
            forall_const(
                ctx,
                &ast_refs,
                &[],
                &complete_ahltl_encoding(ctx, form, inner, traj, states, mapping)
            )
        }
        _ => inner
    }
}


/****************************
*
*   HLTL Encoding Functions
*
****************************/

fn generate_quantified_encoding<'ctx>(ctx: &'ctx Context, formula: &AstNode, paths: &Vec<Vec<EnvState<'ctx>>>, path_encodings: &Vec<Bool<'ctx>>, mapping: &HashMap<&str, usize>, inner: Bool<'ctx>) -> Bool<'ctx> {
    println!("Formula: {:#?}", formula);
    match formula {
        AstNode::HAQuantifier {form, identifier} => {
            let idx = mapping.get(identifier as &str).unwrap();
            let selected_path = &paths[*idx];
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
            let selected_path = &paths[*idx];
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
        _ => {
            //println!("{:#?}", inner);
            inner
        }
    }
}

fn generate_hltl_encoding<'env, 'ctx>(envs: &'env Vec<SMVEnv<'ctx>>, formula: &AstNode, paths: Vec<Vec<EnvState<'ctx>>>, path_encodings: Vec<Bool<'env>>, sem: Semantics, witness: bool) -> Bool<'env> {
    // If witness is set, the formula is already negated
    let ctx = envs[0].ctx;
    // Unroll the formula first
    let inner_ltl = unroll_hltl_formula(envs, formula, &paths, &sem);
    // Construct the inner encoding
    let inner = generate_inner_encoding(ctx, formula, &path_encodings, inner_ltl.clone(), 0);
    // Get the mapping
    let mapping = create_path_mapping(formula, 0);
    // Build the complete encoding
    // Do we look for a witness?
    if witness {
        generate_quantified_encoding(ctx, strip_leading_existentials(formula), &paths, &path_encodings, &mapping, inner.clone())
    }else {
        generate_quantified_encoding(ctx, formula, &paths, &path_encodings, &mapping, inner.clone())
    }

}

pub fn get_verilog_encoding<'env, 'ctx>(envs: &'env Vec<SMVEnv<'ctx>>, models: &Vec<String>, formula: &'ctx AstNode, k: usize, m: Option<usize>, sem: Semantics, witness: bool) -> Bool<'env> {
    let ctx = envs[0].ctx;
    let mut path_constraints : Vec<Bool<'ctx>> = Vec::new();
    let mut states : Vec<Vec<EnvState<'ctx>>> = Vec::new();
    let mut bounded_vars : Vec<Vec<EnvState<'ctx>>> = Vec::new();
    // Obtain the path mapping from the formula
    let path_mapping = create_path_mapping(formula, 0);
    // Formula variables for each path
    let var_mapping: Vec<HashSet<&str>> = extract_variables(formula, &path_mapping);

    for (idx, model) in models.iter().enumerate() {
        let smt2 = CString::new(model.as_str()).unwrap();
        // Get ast vector of each smtlib - There should be only one
        let ast_vec = unsafe {
            Z3_parse_smtlib2_string(
                ctx.z3_ctx,           // raw Z3_context
                smt2.as_ptr(),
                0,
                std::ptr::null(), std::ptr::null(), // no extra sorts
                0,
                std::ptr::null(), std::ptr::null(), // no extra decls
            )
        };
        // Prevent the ast_vec from getting dropped
        unsafe { Z3_ast_vector_inc_ref(ctx.z3_ctx, ast_vec) };
        // extract the assertion as an Ast node
        let raw_ast = unsafe { Z3_ast_vector_get(ctx.z3_ctx, ast_vec, 0 as u32) };
        // Wrap the raw Z3_ast as a Bool - this is the unrolled path constraint
        let d = unsafe { Bool::wrap(&ctx, raw_ast) };
        // Record current path encoding
        path_constraints.push(d.clone());
        // create unrolled states from AST
        let (unrolled_states, quantified_vars) = verilog_helper::unrolled_states_from_Z3_ast(&d, &var_mapping[idx], k);
        // Record current states
        states.push(unrolled_states);
        // record bounded variables
        bounded_vars.push(quantified_vars);
    }

    if is_hltl(formula) {
        // Unroll the formula first
        let inner_ltl = unroll_hltl_formula(envs, formula, &states, &sem);
        // Construct the inner encoding
        let inner = generate_inner_encoding(ctx, formula, &path_constraints, inner_ltl.clone(), 0);
        // Get the mapping
        let mapping = create_path_mapping(formula, 0);
        // Build the complete encoding
        // Do we look for a witness?
        if witness {
            generate_quantified_encoding(ctx, strip_leading_existentials(formula), &bounded_vars, &path_constraints, &mapping, inner.clone())
        }else {
            generate_quantified_encoding(ctx, formula, &bounded_vars, &path_constraints, &mapping, inner.clone())
        }

    }else {
        // It's an A-HLTL formula
        // Extract M. If it is not provided, panic!
        let m = match m {
            Some(m) => m,
            None => panic!("Unrolling bound of trajectories can not be None!"),
        };
        // The semantics must be halting
        if !matches!(sem, Semantics::Hpes | Semantics::Hopt) {
            panic!("Only halting semantics are allowed for A-HLTL BMC.");
        }
        // Call the AHLTL encoding generator
        generate_ahltl_encoding(envs, formula, states, path_constraints, m, sem, witness)
    }
    
}

pub fn extract_grouped_model(model: &Model) -> Vec<(i32, Vec<(String, String)>)> {
    let re = Regex::new(r".*_(\d+)_(\w+)$").expect("valid regex");

    // Temp list: (state, (var_name, value))
    let mut temp: Vec<(i32, (String, String))> = Vec::new();

    // Iterate declarations in the model
    for decl in model.iter() {
        // We only care about constants (functions with arity 0)
        if decl.arity() != 0 {
            continue;
        }

        let var_name = decl.name();

        // Turn the declaration into a constant AST and read its interpretation.
        // `apply(&[])` yields the constant; try `get_const_interp`, then fall back to `eval`.
        let const_ast: Dynamic = decl.apply(&[]);
        let value_ast = model
            .get_const_interp(&const_ast)
            .or_else(|| model.eval(&const_ast, true));

        let val_str = value_ast
            .map(|v| v.to_string())
            .unwrap_or_else(|| "undef".to_string());

        if let Some(caps) = re.captures(&var_name) {
            let state: i32 = caps.get(1).unwrap().as_str().parse().unwrap_or(-1);
            temp.push((state, (var_name, val_str)));
        } else {
            // Uncomment if you want to see non-matching names:
            eprintln!("unmatched: {}", var_name);
        }
    }

    // Sort by state, then variable name
    temp.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1 .0.cmp(&b.1 .0)));

    // Group into the requested Vec format
    let mut grouped: Vec<(i32, Vec<(String, String)>)> = Vec::new();
    for (state, (var, val)) in temp {
        if let Some(last) = grouped.last_mut() {
            if last.0 == state {
                last.1.push((var, val));
                continue;
            }
        }
        grouped.push((state, vec![(var, val)]));
    }

    grouped
}