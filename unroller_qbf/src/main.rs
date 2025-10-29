use regex::Regex;
use std::collections::HashMap;
use z3::SortKind;
use z3::ast::Ast;
use expressions::*;
use logging::*;
use ir::*;
use z3::ast::{Bool, Int, Dynamic};
use z3::{Config, Context, Sort};
use utils::*;
use std::fs;
use std::fs::File;
use std::path::Path;
use std::process;
use std::collections::HashSet;
use fsm::to_qcir_string;
use fsm::to_qcir_unrolled;
use fsm::to_qcir_unrolled_ahltl;
use fsm::unroll_ltl;
use expressions::exprparser::{parse_hyperltl, parse_ahltl};
use expressions::Literal::{Atom, NegAtom};
use expressions::{Literal as Lit, Variable, Quant};
use expressions::Expression::*;
use flags::flags::parse_flags;

pub type PredMap = HashMap<String, Expression>;

pub fn gen_qcir<'env, 'ctx>(
    envs: &'env Vec<SMVEnv<'ctx>>,
    files: &Vec<&str>, 
    formula: &String, 
    bound: usize, 
    debug: bool, 
    semantics: &str,
    out_path: &Path,
) {
    let mut expr_vec: Vec<Box<Expression>> = vec![];
    let mut complete_bit_map : HashMap<String, usize> = HashMap::new();
    let mut init_map: HashMap<String, Vec<String>> = HashMap::new();
    let mut init_map_vec: Vec<(String, HashMap<String, Vec<String>>)> = Vec::new(); //[(filename, init_map),...]
    let mut models: Vec<(String,String)> = Vec::new(); // all init maps in a vec
    let mut models_expr: Vec<(Expression,Expression)> = Vec::new(); // all init maps in a vec

    // START: iterate through each SMVEnv, build the 
    for (i, (env, file)) in envs.iter().zip(files.iter()).enumerate() {
        let mut max_bit_map: HashMap<String, usize> = HashMap::new();
        let variables = env.get_variables(); // returns &HashMap<String, Variable>

        // AUX: Build bit map: var name -> minimum bitwidth (for later bit-blasting)
        for (var_name, v) in variables {
            // println!("var: {:?}, {:?}", var_name, v);
            if let VarType::Int { upper: Some(max_val), .. } = v.sort {
                let bitwidth = (64 - (max_val).leading_zeros()) as usize;
                max_bit_map.insert(var_name.to_string(), bitwidth);
            }
        }

        // BUILD: initial conditions
        let pred_names: HashSet<String> = env
            .get_predicates()
            .keys()
            .map(|s| s.to_string())
            .collect();
        let (states, _path_constraint) = env.generate_symbolic_path(1, Some("init"));
        let z3_constraints = env.generate_initial_constraints(&states);
        let mut init_exprs = Vec::new();
        for c in z3_constraints {
            let dyn_node = Dynamic::from_ast(&c);
            // println!("DEBUG dyn_node: {dyn_node}");
            let raw_expr = dyn_to_expr("(init)", &dyn_node, /*is_primed=*/false, &max_bit_map);
            let init_expr = simplify_trivial_iff(&raw_expr);

            // Skip if this clause refers to any predicate atom
            if contains_predicate_atom(&init_expr, &pred_names) {
                continue;
            }
            init_exprs.push(Box::new(init_expr));
        }

        let full_init_expr = if init_exprs.is_empty() {
            Expression::True
        } else {
            Expression::MAnd(init_exprs.clone())
        };
        
        // Build transition conditions 
        let dummy_state = env.make_dummy_state(env.get_context());
        for (var_name, transitions_vec) in env.get_transitions() {
            // let var_name = *var_name;
            // if transitions_vec.is_empty() {
            //     if let Some(var) = variables.get(var_name) {
            //         if let Some(expr) = full_nondet_update_expr(var_name, var, &max_bit_map) {
            //             expr_vec.push(Box::new(expr));
            //         } else {
            //             expr_vec.push(Box::new(Expression::True));
            //         }
            //     }
            //     continue;
            // }

            let mut covered: Vec<Expression> = Vec::new(); // to be use in TRUE cases
            for (i, (guard_fn, update_fn)) in transitions_vec.iter().enumerate() {

                // 1) Evaluate once
                let guard_ret  = guard_fn(env, env.get_context(), &dummy_state);
                let update_ret = update_fn(env, env.get_context(), &dummy_state);

                // DEBUG: dynamic nodes
                // println!(">>> Dyn nodes: ");
                // println!("Guard:  {:?}", guard_ret);
                // println!("Update: {:?}\n", update_ret);

                let next_expr_fast = fast_next_expr_from_return(
                                        &update_ret, var_name, &max_bit_map);

                // 2) Convert once
                let ctx = env.get_context();

                // 3) Use both if available
                match (
                    ret_to_dynamic_result(ctx, env, &dummy_state, var_name,  guard_ret),
                    ret_to_dynamic_result(ctx, env, &dummy_state, var_name, update_ret),
                ) {
                    // convert both dynamic nodes 
                    (Ok(guard_node), Ok(update_node)) =>
                    {
                        // println!("Dyn Guard:  {:?}", guard_node);
                        // println!("Dyn Update:  {:?}", update_node);
                        
                        // Expressions of Guard and Update 
                        let mut curr_guard = dyn_to_expr(&var_name, &guard_node, false, &max_bit_map); 
                        let mut next_expr  = if let Some(e) = next_expr_fast {
                            e // ★ literal true/false or single int constant case
                        } else {
                            // fallback: convert dynamic → Expression
                            dyn_to_expr(&var_name, &update_node, true, &max_bit_map)
                        };


                        curr_guard = simplify_trivial_iff(&curr_guard);
                        next_expr  = simplify_trivial_iff(&next_expr);

                        // println!("Guard:   {:?}\n", expression_to_string(&curr_guard));
                        // println!("Update:  {:?}\n", expression_to_string(&next_expr));

                        let next_var = Expression::Literal(Lit::Atom(format!("{}'", var_name)));

                        // literal fast-path flag
                        let is_literal = matches!(
                            next_expr,
                            Expression::Literal(Lit::Atom(_)) |
                            Expression::Literal(Lit::NegAtom(_))
                        );

                        // Handling the TRUE case
                        if curr_guard == Expression::True {
                                if let Some(i_ast) = update_node.as_int() {
                                    if update_node.children().len() == 0 {
                                        let key: &str = *var_name;
                                        let bw = *max_bit_map.get(key).expect("missing bitwidth");
                                        next_expr = build_bitblasted_self_eq(key, bw);

                                    }   
                                }

                            if !covered.is_empty() {
                                // guard := ¬(∨ covered)
                                let covered_or = Expression::MOr(
                                    covered.iter().cloned().map(Box::new).collect());
                                let guard = Expression::Neg(Box::new(covered_or));
                                expr_vec.push(Box::new(Expression::Implies(
                                    Box::new(guard), 
                                    Box::new(next_expr))));
                            } else {
                                // the "TRUE" exhausive case
                                if is_literal {
                                    // True ⇒ next_expr  ≡ next_expr
                                    expr_vec.push(Box::new(next_expr.clone()));
                                } else {
                                    // original behavior: just (next_var ↔ next_expr)
                                    // let next_eq = Expression::Iff(
                                        // Box::new(next_expr.clone()),
                                        // Box::new(next_var.clone()));
                                    expr_vec.push(Box::new(next_expr.clone()));

                                    // expr_vec.push(Box::new(next_eq));
                                }
                            }

                            
                   
                        } else {
                            // Non-trivial guard: add to covered and guard the clause
                            covered.push(curr_guard.clone());

                            if is_literal {
                                // curr_guard ⇒ next_expr
                                expr_vec.push(Box::new(Expression::Implies(
                                    Box::new(curr_guard.clone()),
                                    Box::new(next_expr.clone()),
                                )));
                            } else {
                                // curr_guard ⇒ (next_var ↔ next_expr)
                                // let next_eq = Expression::Iff(
                                    // Box::new(next_var.clone()), 
                                    // Box::new(next_expr.clone()));
                                expr_vec.push(Box::new(Expression::Implies(
                                    Box::new(curr_guard.clone()),
                                    Box::new(next_expr.clone()),
                                )));
                            }
                        } 
                    } 
                    (Err(e1), Err(e2)) => {
                        eprintln!("guard conversion failed: {e1}");
                        eprintln!("update conversion failed: {e2}");
                        // handle both errors (skip, return, etc.)
                    }

                    (Err(e), _) => {
                        eprintln!("guard conversion failed: {e}");
                        // handle/return as appropriate
                    }

                    (_, Err(e)) => {
                        eprintln!("update conversion failed: {e}");
                        // handle/return as appropriate
                    }
                }
            }
        }

        // DEBUG: initial conditions
        // println!(">>> INITIAL CONDITIONS: ");
        // for (idx, expr) in init_exprs.iter().enumerate() {
        //     println!("  [{}] {}", idx, expression_to_string(&*expr));
        // }
        

        //// DEBUG: transitions
        // println!(">>> TRANSITIONS: ");
        // for (i, e) in expr_vec.iter().enumerate() {
        //     println!("  [{}] {}", i, expression_to_string(&*e));
        // }

        let full_trans_expr = Expression::MAnd(expr_vec.clone());
        expr_vec.clear();
        complete_bit_map.extend(
            max_bit_map.iter().map(|(k, v)| (k.clone(), *v as usize))
        );
        let expr_pair = (full_init_expr, full_trans_expr);
        models_expr.push(expr_pair);
    }


    if (is_ahltl(formula)) {
        let mut quantifiers: Vec<(String, String)> = Vec::new();
        let parsed = parse_ahltl(formula, &complete_bit_map, bound).expect("AHLTL parse failed");
        let quants = parsed.prefix;
        let form = parsed.ahltl_expr;
        let all_phi_pos = parsed.all_phi_pos;


        let mut predicates_map = PredMap::new();
        for (i, env) in envs.iter().enumerate(){
            for (name, mk) in env.get_predicates().iter() {
                let path = &quants[i].1;
                let ctx: &'ctx Context = env.get_context();
                let dummy_state = env.make_dummy_state(env.get_context());
                // 1) Z3 Bool AST for the predicate body
                let z3b: Bool<'ctx> = mk(env, ctx, &dummy_state);

                // 2) Convert to your Expression (no priming inside predicates)
                let dynb = Dynamic::from_ast(&z3b);
                let body_expr = dyn_to_expr(name, &dynb, /*is_primed=*/false, &complete_bit_map);

                // 3) Instantiate for each time
                for t in 0..=bound {
                    let key = stamp_name_with(path, t, name); // "halt[A][0]"
                    let val = stamp_expr_at_time_with_path(&body_expr, path, t);
                    predicates_map.insert(key, val);
                }
            }
        }

        let final_formula = subst_predicates_fixpoint(&form, &predicates_map);
        // let final_formula = Expression::True; // <-- temp

        let qcir = to_qcir_unrolled_ahltl(&models_expr, &quants, &final_formula, &predicates_map, &all_phi_pos, bound)
                            .expect("QCIR unrolling failed");;

        if let Some(dir) = out_path.parent() {
            if !dir.as_os_str().is_empty() {
                fs::create_dir_all(dir).expect("create_dir_all failed");
            }
        }

        fs::write(out_path, qcir).expect("QCIR file writing failed");

        if debug {
            eprintln!("[gen_qcir_to_file] wrote {}", out_path.display());
        }



    } else {
        // println!("Given formula is HLTL");
        let mut quantifiers: Vec<(String, String)> = Vec::new();
        let parsed = parse_hyperltl(formula, &complete_bit_map).expect("HLTL parse failed");
        let form = parsed.formula;
        let quants = parsed.prefix;
        // println!("\nParsed formula:\n {:?}", form);
        
        let mut predicates_map = PredMap::new();
        for (i, env) in envs.iter().enumerate(){
            for (name, mk) in env.get_predicates().iter() {
                let path = &quants[i].1;
                let ctx: &'ctx Context = env.get_context();
                let dummy_state = env.make_dummy_state(env.get_context());
                // 1) Z3 Bool AST for the predicate body
                let z3b: Bool<'ctx> = mk(env, ctx, &dummy_state);

                // 2) Convert to your Expression (no priming inside predicates)
                let dynb = Dynamic::from_ast(&z3b);
                let body_expr = dyn_to_expr(name, &dynb, /*is_primed=*/false, &complete_bit_map);

                // 3) Instantiate for each time
                for t in 0..=bound {
                    let key = stamp_name_with(path, t, name); // "halt[A][0]"
                    let val = stamp_expr_at_time_with_path(&body_expr, path, t);
                    predicates_map.insert(key, val);
                }
            }
        }

        // Check if the formula is valid
        // let formula_expr = parse_inner_ltl(&form);
        let formula_unrolled = unroll_ltl(&form, bound);
        let final_formula = subst_predicates_fixpoint(&formula_unrolled, &predicates_map);
        // println!("LTL formula: {:?}", expression_to_string(&form));
        // println!("final unrolled formula: {:?}", expression_to_string(&final_formula));

        // Now the types line up:
        let qcir = to_qcir_unrolled(&models_expr, &predicates_map, &quants, &final_formula, bound)
                            .expect("QCIR unrolling failed");;

        if let Some(dir) = out_path.parent() {
            if !dir.as_os_str().is_empty() {
                fs::create_dir_all(dir).expect("create_dir_all failed");
            }
        }

        fs::write(out_path, qcir).expect("QCIR file writing failed");

        if debug {
            eprintln!("[gen_qcir_to_file] wrote {}", out_path.display());
        }
    }
    
}



/* 
If `expr` is `MOr([ ... (X <-> true) ..., ... (X <-> false) ..., ... ])`,
rewrite those two IFFs into a single `(X | ~X)`. Other disjuncts remain.
Returns the (possibly) simplified expression.
(No recursive descent here; call this after your building step, or wrap it in a recursive simplifier.)
*/
pub fn simplify_trivial_iff(expr: &Expression) -> Expression {
    use Expression::*;

    // Helper: detect an IFF of form (Atom(X) <-> True/False), allowing either side
    fn iff_atom_bool(e: &Expression) -> Option<(String, bool)> {
        use Expression::*;
        match e {
            Iff(a, b) => {
                match (&**a, &**b) {
                    (Literal(Lit::Atom(x)), True)  => Some((x.clone(), true)),
                    (Literal(Lit::Atom(x)), False) => Some((x.clone(), false)),
                    (True,  Literal(Lit::Atom(x)))  => Some((x.clone(), true)),
                    (False, Literal(Lit::Atom(x)))  => Some((x.clone(), false)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    // Only act on MOr; everything else unchanged
    let xs = match expr {
        MOr(v) => v,
        _ => return expr.clone(),
    };

    // 1) Find which variables have both (X<->true) and (X<->false)
    let mut flags: HashMap<String, (bool, bool)> = HashMap::new();
    for term in xs.iter() {
        if let Some((var, is_true)) = iff_atom_bool(term) {
            let entry = flags.entry(var).or_insert((false, false));
            if is_true { entry.0 = true; } else { entry.1 = true; }
        }
    }

    // Vars to replace with X | ~X
    let mut winners: HashSet<String> = flags
        .into_iter()
        .filter_map(|(v, (t, f))| if t && f { Some(v) } else { None })
        .collect();

    if winners.is_empty() {
        // nothing to do
        return expr.clone();
    }

    // 2) Rebuild MOr: skip the matched IFFs for winners; keep others;
    //    add one (X | ~X) per winner at the end.
    let mut new_terms: Vec<Box<Expression>> = Vec::with_capacity(xs.len());

    for term in xs.iter() {
        if let Some((var, _tf)) = iff_atom_bool(term) {
            if winners.contains(&var) {
                // skip both (X<->true) and (X<->false); we'll add (X | ~X) once later
                continue;
            }
        }
        new_terms.push(term.clone());
    }

    // Append simplified (X | ~X) for each winner
    for var in winners.drain() {
        let x = Expression::Literal(Lit::Atom(var.clone()));
        let nx = Expression::Neg(Box::new(Expression::Literal(Lit::Atom(var))));
        new_terms.push(Box::new(Expression::Or(Box::new(x), Box::new(nx))));
    }

    Expression::MOr(new_terms)
}


/* 
Main method to convert a z3 dynamic node to Expression
*/
pub fn dyn_to_expr(
    var_name: &str,
    node: &Dynamic, 
    is_primed: bool, 
    max_bit_map: &HashMap<String, usize>
) -> Expression {
    let sort_kind = node.get_sort().kind();
    let decl_name = node.decl().name().to_string();

    // DEBUG
    // println!("\nOWNER NAME: {:?}", var_name);
    // println!("Sort: {:?}", node.get_sort());
    // println!("SMT-LIB: {}", node.to_string());
    // println!("Children count: {}", node.num_children());

    match sort_kind {
        SortKind::Bool => {
            // Quick guard: must be Bool-typed at the top.
            debug_assert_eq!(node.get_sort().kind(), SortKind::Bool, "expected Bool node");

            let decl_name = node.decl().name().to_string();
            let arity = node.num_children();

            match arity {
                // ---------- (1) LEAF ----------
                0 => {
                    // literal true/false?
                    if let Some(b) = node.as_bool().and_then(|b| b.as_bool()) {
                        return if b { Expression::True } else { Expression::False };
                    }
                    // otherwise: an atomic boolean symbol
                    let name = clean_var_name(&decl_name, is_primed);
                    return Expression::Literal(Lit::Atom(name));
                }

                // ---------- UNARY / BINARY / N-ARY ----------
                _ => {
                    // If ANY Int appears inside, we’re in case (2) — enumerate.
                    if has_int_in_subtree(node) {
                        // return enumerate_int_conditions_for_bool(node, max_bit_map);
                        // println!("start parsing: {}", node.to_string());
                        return dyn_mixed_bool_to_expr(node, is_primed, max_bit_map);
                    }

                    // Otherwise purely-boolean → case (3)
                    // (This handles and/or/not/=/if/ite and any other Bool-only structure.)
                    return dyn_bool_to_expression(node, is_primed);
                }
            }
        } 
        SortKind::Int => {
            // hint: guard will always be a Boolean node. 
            return dyn_int_to_transition(var_name, node, max_bit_map);
        } 
        _ => {
            panic!("QBF unrolling error: sort_kind {:?} is unsupported", node.get_sort().kind());
        }
    }
}



/// Small integer expression AST
#[derive(Clone, Debug)]
enum IntExpr {
    Var(String),
    Const(i64),
    Add(Box<IntExpr>, Box<IntExpr>),
    Sub(Box<IntExpr>, Box<IntExpr>),
    Mul(Box<IntExpr>, Box<IntExpr>),
    Div(Box<IntExpr>, Box<IntExpr>),
    Mod(Box<IntExpr>, Box<IntExpr>),
}

#[derive(Copy, Clone, Debug)]
enum CmpOp { Eq, Lt, Le, Gt, Ge }

#[derive(Clone, Debug)]
enum BoolExpr {
    True,
    False,
    Var(String),
    And(Vec<BoolExpr>),
    Or(Vec<BoolExpr>),
    Not(Box<BoolExpr>),
    Cmp(CmpOp, IntExpr, IntExpr), // integer comparison
    // (Optional) Bool vars/structs are ignored for enumeration in this utility
}

fn has_int_in_subtree(node: &Dynamic) -> bool {
    if node.get_sort().kind() == SortKind::Int { return true; }
    node.children().iter().any(has_int_in_subtree)
}

/// Convert a Z3 Dynamic (Sort:Int) to IntExpr, cleaning var names (drop !k, primes, etc.).
fn dyn_int_to_ast(node: &Dynamic) -> IntExpr {
    // Constant?
    if let Some(i) = node.as_int().and_then(|ia| ia.as_i64()) {
        return IntExpr::Const(i);
    }

    // Variable (0 children): clean the decl name.
    if node.children().is_empty() {
        let raw = node.decl().name().to_string();
        let name = clean_var_name(&raw, /*is_primed=*/false);
        return IntExpr::Var(name);
    }

    // Operator with children
    let op = node.decl().name().to_string();
    let ch = node.children();

    // Support unary minus by rewriting to (0 - x)
    let bin = |a: &Dynamic, b: &Dynamic, tag: &str| -> IntExpr {
        let la = Box::new(dyn_int_to_ast(a));
        let rb = Box::new(dyn_int_to_ast(b));
        match tag {
            "+" => IntExpr::Add(la, rb),
            "-" => IntExpr::Sub(la, rb),
            "*" => IntExpr::Mul(la, rb),
            "/" => IntExpr::Div(la, rb),
            "mod" => IntExpr::Mod(la, rb),
            _ => panic!("illegal operator '{tag}' in int expression '{}'", node.to_string()),
        }
    };

    match (op.as_str(), ch.len()) {
        ("-", 1) => bin(&zero_like(node), &ch[0], "-"), // unary minus -> (0 - x)
        (op2, 2) => bin(&ch[0], &ch[1], op2),
        _ => panic!("illegal operator/arity in int expression '{}'", node.to_string()),
    }
}

// ---- Build BoolExpr from Z3 Dynamic (Bool), cleaning names for ints inside ----
fn dyn_bool_to_ast(node: &Dynamic) -> BoolExpr {
    match node.get_sort().kind() {
        SortKind::Bool => {
            // Literal true/false?
            if let Some(b) = node.as_bool().and_then(|ba| ba.as_bool()) {
                return if b { BoolExpr::True } else { BoolExpr::False };
            }

            // Leaf boolean symbol (no children) -> return as a literal/variable
            if node.children().is_empty() {
                let name = clean_var_name(&node.decl().name().to_string(), /*is_primed=*/false);
                return BoolExpr::Var(name); // or BoolExpr::Atom(name) if that's your enum
            }

            // recursive cases
            let op = node.decl().name().to_string();
            let ch = node.children();
            match op.as_str() {
                "and" => BoolExpr::And(ch.iter().map(dyn_bool_to_ast).collect()),
                "or"  => BoolExpr::Or(ch.iter().map(dyn_bool_to_ast).collect()),
                "not" => {
                    assert_eq!(ch.len(), 1);
                    BoolExpr::Not(Box::new(dyn_bool_to_ast(&ch[0])))
                }
                "=" | "<" | "<=" | ">" | ">=" => {
                    assert_eq!(ch.len(), 2);
                    // We only support int comparisons here
                    let l = dyn_int_to_ast(&ch[0]);
                    let r = dyn_int_to_ast(&ch[1]);
                    let cop = match op.as_str() {
                        "="  => CmpOp::Eq,
                        "<"  => CmpOp::Lt,
                        "<=" => CmpOp::Le,
                        ">"  => CmpOp::Gt,
                        ">=" => CmpOp::Ge,
                        _ => unreachable!(),
                    };
                    BoolExpr::Cmp(cop, l, r)
                }
                // Other boolean structure (like boolean equality/vars) -> not handled in enumeration
                other => {
                    panic!("illegal boolean operator '{other}' for int-enumeration in '{}'", node.to_string());
                }
            }
        }
        other => panic!("dyn_bool_to_ast expected Bool node, got {:?}", other),
    }
}

/// Build a Dynamic Int constant 0 with same context (for unary minus lowering).
fn zero_like<'ctx>(node: &Dynamic<'ctx>) -> Dynamic<'ctx> {
    let ctx = node.get_ctx();
    Int::from_i64(ctx, 0).into()
}

/// Evaluate IntExpr under an environment (var -> value). Returns None on div-by-zero/mod-by-zero
fn eval_int(expr: &IntExpr, env: &HashMap<String, i64>) -> Option<i64> {
    use IntExpr::*;
    match expr {
        Var(v)      => env.get(v).cloned(),
        Const(c)    => Some(*c),
        Add(a,b)    => Some(eval_int(a, env)? + eval_int(b, env)?),
        Sub(a,b)    => Some(eval_int(a, env)? - eval_int(b, env)?),
        Mul(a,b)    => Some(eval_int(a, env)? * eval_int(b, env)?),
        Div(a,b)    => {
            let x = eval_int(a, env)?;
            let y = eval_int(b, env)?;
            if y == 0 { None } else { Some(x / y) }
        }
        Mod(a,b)    => {
            let x = eval_int(a, env)?;
            let y = eval_int(b, env)?;
            if y == 0 { None } else { Some(x % y) }
        }
    }
}


fn eval_cmp(op: CmpOp, a: i64, b: i64) -> bool {
    match op {
        CmpOp::Eq => a == b,
        CmpOp::Lt => a <  b,
        CmpOp::Le => a <= b,
        CmpOp::Gt => a >  b,
        CmpOp::Ge => a >= b,
    }
}

fn eval_bool(expr: &BoolExpr, env: &HashMap<String, i64>) -> Option<bool> {
    use BoolExpr::*;
    match expr {
        True  => Some(true),
        False => Some(false),
        Not(x) => Some(!eval_bool(x, env)?),
        And(xs) => {
            let mut acc = true;
            for x in xs {
                acc = acc && eval_bool(x, env)?;
                if !acc { break; }
            }
            Some(acc)
        }
        Or(xs) => {
            let mut acc = false;
            for x in xs {
                acc = acc || eval_bool(x, env)?;
                if acc { break; }
            }
            Some(acc)
        }
        Cmp(op, l, r) => {
            let a = eval_int(l, env)?;
            let b = eval_int(r, env)?;
            Some(eval_cmp(*op, a, b))
        },
        &BoolExpr::Var(_) => todo!()
    }
}

/// Collect variable names from IntExpr (unique).
fn collect_vars_int(expr: &IntExpr, out: &mut HashSet<String>) {
    use IntExpr::*;
    match expr {
        Var(v)   => { out.insert(v.clone()); }
        Const(_) => {}
        Add(a,b) | Sub(a,b) | Mul(a,b) | Div(a,b) | Mod(a,b) => {
            collect_vars_int(a, out);
            collect_vars_int(b, out);
        }
    }
}

fn collect_vars_bool(expr: &BoolExpr, out: &mut HashSet<String>) {
    use BoolExpr::*;
    match expr {
        True|False => {}
        Not(x) => collect_vars_bool(x, out),
        And(xs) | Or(xs) => for x in xs { collect_vars_bool(x, out); }
        Cmp(_, l, r) => {
            collect_vars_int(l, out);
            collect_vars_int(r, out);
        },
        Var(v) => {
            let cleaned = clean_var_name(v, false);
            out.insert(cleaned);
        }
    }
}

/// Recursively translate a pure Boolean `Dynamic` node into `Expression`.
/// Assumes the whole subtree is Boolean (no Int/BV).
pub fn dyn_bool_to_expression(node: &Dynamic, is_primed: bool) -> Expression {
    // Base cases: literal true/false or variable-like leaf
    if node.children().is_empty() {
        if node.get_sort().kind() == SortKind::Bool {
            if let Some(b) = node.as_bool().and_then(|b| b.as_bool()) {
                return if b { Expression::True } else { Expression::False };
            }
        }
        // Boolean symbol/atom
        let name = clean_var_name(&node.decl().name().to_string(), is_primed);
        return Expression::Literal(Lit::Atom(name));
    }

    // Recursive cases
    let decl = node.decl().name().to_string();
    let kids = node.children();
    let args: Vec<Expression> = kids
        .iter()
        .map(|c| dyn_bool_to_expression(&Dynamic::from_ast(c), is_primed))
        .collect();

    match decl.as_str() {
        "and" => Expression::MAnd(args.into_iter().map(Box::new).collect()),
        "or"  => Expression::MOr(args.into_iter().map(Box::new).collect()),
        "not" => {
            assert!(args.len() == 1, "not expects 1 arg, got {}", args.len());
            negate_expr(args.into_iter().next().unwrap())
        }

        // Pure-boolean equality → IFF
        "=" => {
            assert!(args.len() == 2, "= expects 2 args, got {}", args.len());
            let lhs = args[0].clone();
            let rhs = args[1].clone();

            if lhs == Expression::True {
                rhs
            } else if rhs == Expression::True {
                lhs
            } else if lhs == Expression::False {
                negate_expr(rhs)
            } else if rhs == Expression::False {
                negate_expr(lhs)
            } else {
                Expression::Iff(Box::new(lhs), Box::new(rhs))
            }
        }

        // Conditional forms
        // if(cond, then)  ≡ (cond → then)
        "if" => {
            assert!(args.len() == 2, "if expects 2 args, got {}", args.len());
            Expression::Implies(Box::new(args[0].clone()), Box::new(args[1].clone()))
        }
        // ite(cond, then, else) ≡ (cond → then) ∧ (¬cond → else)
        "ite" => {
            assert!(args.len() == 3, "ite expects 3 args, got {}", args.len());
            let cond = args[0].clone();
            let thn  = args[1].clone();
            let els  = args[2].clone();
            Expression::And(
                Box::new(Expression::Implies(Box::new(cond.clone()), Box::new(thn))),
                Box::new(Expression::Implies(Box::new(negate_expr(cond)), Box::new(els))),
            )
        }

        // Anything else would be non-boolean or unsupported in this helper
        other => panic!("dyn_bool_to_expression: unsupported boolean op '{}'", other),
    }
}


/// Convert a *boolean* Z3 node (possibly mixing int & bool subterms) into `Expression`.
pub fn dyn_mixed_bool_to_expr(
    node: &Dynamic,
    is_primed: bool,
    max_bit_map: &HashMap<String, usize>,
) -> Expression {
    // Must be a Bool at the root.
    if node.get_sort().kind() != SortKind::Bool {
        panic!("dyn_mixed_bool_to_expr expects Bool node, got {:?}", node.get_sort().kind());
    }

    // Literal true/false?
    if let Some(b) = node.as_bool().and_then(|ba| ba.as_bool()) {
        return if b { Expression::True } else { Expression::False };
    }

    let op = node.decl().name().to_string();
    let ch = node.children();

    // Leaf boolean var (no children): just its cleaned name.
    if ch.is_empty() {
        let name = clean_var_name(&op, is_primed);
        return match name.as_str() {
            "true"  => Expression::True,
            "false" => Expression::False,
            _       => Expression::Literal(Lit::Atom(name)),
        };
    }

    match op.as_str() {
        "and" => {
            let parts: Vec<Box<Expression>> =
                ch.iter().map(|c| dyn_mixed_bool_to_expr(c, is_primed, max_bit_map)).map(Box::new).collect();
            if parts.is_empty() { Expression::True }
            else if parts.len() == 1 { *parts.into_iter().next().unwrap() }
            else { Expression::MAnd(parts) }
        }
        "or" => {
            let parts: Vec<Box<Expression>> =
                ch.iter().map(|c| dyn_mixed_bool_to_expr(c, is_primed, max_bit_map)).map(Box::new).collect();
            if parts.is_empty() { Expression::False }
            else if parts.len() == 1 { *parts.into_iter().next().unwrap() }
            else { Expression::MOr(parts) }
        }
        "not" => {
            assert_eq!(ch.len(), 1);
            let inner = dyn_mixed_bool_to_expr(&ch[0], is_primed, max_bit_map);
            negate_expr(inner)
        }

        // Mixed cases (boolean comparisons possibly over ints): delegate to your
        // already-bitblasting comparator encoder.
        "=" | "<" | "<=" | ">" | ">=" => {
            assert!(ch.len() == 2);
            let l = &ch[0];
            let r = &ch[1];

            // arithmetic term = Int sort with children (not just a leaf var or const)
            let is_arith = |d: &Dynamic| d.get_sort().kind() == SortKind::Int && !d.children().is_empty();

            if is_arith(l) || is_arith(r) {
                // Enumerate all integer assignments from max_bit_map that make this
                // comparator true, returning an MOr of bit-blasted equalities.
                return enumerate_int_conditions_for_bool(node, max_bit_map);
            }

            // otherwise use the fast path you already have
            let hint = var_name_hint_from_children(l, r).unwrap_or_default();
            return encode_cmp_dyn(op.as_str(), l, r, is_primed, max_bit_map, &hint);
        }

        // Optional: a boolean ITE — encode as (c→t) ∧ (¬c→e).
        "ite" => {
            assert!(ch.len() == 3, "ite(cond, then, else) expected");
            let c = dyn_mixed_bool_to_expr(&ch[0], is_primed, max_bit_map);
            let t = dyn_mixed_bool_to_expr(&ch[1], is_primed, max_bit_map);
            let e = dyn_mixed_bool_to_expr(&ch[2], is_primed, max_bit_map);
            Expression::And(
                Box::new(Expression::Implies(Box::new(c.clone()), Box::new(t))),
                Box::new(Expression::Implies(Box::new(negate_expr(c)), Box::new(e))),
            )
        }

        // Fallback: treat unknown boolean operator as a symbolic atom.
        other => {
            let name = clean_var_name(other, is_primed);
            Expression::Literal(Lit::Atom(format!("UNKNOWN_BOOL({})", name)))
        }
    }
}

/// Enumerate all integer assignments that satisfy `bool_node` (Z3 Bool)
/// and return a disjunction of conjunctions of bit-blasted equalities like:
///     (x=5 ∧ y=0) ∨ (x=6 ∧ y=0) ∨ ...
///
/// - Only runs if there is any Int node in the subtree; otherwise returns `None` (no enumeration).
/// - Domains are unsigned 0..(2^bw - 1), where `bw` is from `max_bit_map`.
/// - Equalities in the result are **unprimed**.
pub fn enumerate_int_conditions_for_bool(
    bool_node: &Dynamic,
    max_bit_map: &HashMap<String, usize>,
) -> Expression {

    // 1) Build a cleaned BoolExpr with Int subterms
    let bex = dyn_bool_to_ast(bool_node);

    // 2) Collect integer variables
    let mut vset = HashSet::<String>::new();
    collect_vars_bool(&bex, &mut vset);
    let mut vars: Vec<String> = vset.into_iter().collect();
    vars.sort();

    // 3) Build domains from max_bit_map (unsigned)
    let domains: Vec<Vec<i64>> = vars.iter().map(|v| {
        let bw = *max_bit_map
            .get(v)
            .unwrap_or_else(|| panic!("missing bitwidth for int var '{}'", v));
        let max = (1_i64 << bw) - 1;
        (0..=max).collect()
    }).collect();

    // 4) Enumerate
    let mut disjuncts: Vec<Box<Expression>> = Vec::new();
    let mut idx = vec![0usize; vars.len()];
    let mut env = HashMap::<String, i64>::with_capacity(vars.len());

    'outer: loop {
        env.clear();
        for (i, v) in vars.iter().enumerate() {
            env.insert(v.clone(), domains[i][idx[i]]);
        }

        if let Some(true) = eval_bool(&bex, &env) {
            // Build ∧ (v == env[v]) and push as a disjunct
            let mut lanes: Vec<Box<Expression>> = Vec::with_capacity(vars.len());
            for (i, v) in vars.iter().enumerate() {
                let bw = *max_bit_map.get(v).unwrap();
                lanes.push(Box::new(build_bitblasted_equality(v, domains[i][idx[i]], bw, false)));
            }
            let conj = if lanes.len() == 1 { *lanes.pop().unwrap() } else { Expression::MAnd(lanes) };
            disjuncts.push(Box::new(conj));
        }

        // advance cartesian product
        if vars.is_empty() { break; }
        let mut k = vars.len();
        while k > 0 {
            k -= 1;
            idx[k] += 1;
            if idx[k] < domains[k].len() {
                break;
            }
            idx[k] = 0;
            if k == 0 { break 'outer; }
        }
    }

    // 5) Return MOr of all satisfying cases (or False if none)
    if disjuncts.is_empty() {
        Expression::False
    } else if disjuncts.len() == 1 {
        *disjuncts.pop().unwrap()
    } else {
        Expression::MOr(disjuncts)
    }
}

/// Enumerate all assignments over the product of variable domains and build a big ∧ of
/// ((∧ v (v == val_v)) -> (owner' == result))
///
/// - `owner` is the LHS variable to assign (primed in consequent)
/// - `owner_bw` must exist in `max_bit_map[owner]`
/// - Domains are 0 .. (1<<bw)-1 (unsigned)
pub fn dyn_int_to_transition(
    owner: &str,
    node: &Dynamic,
    max_bit_map: &HashMap<String, usize>,
) -> Expression {
    // 1) to IntExpr
    let ie = dyn_int_to_ast(node);

    // 2) collect vars and their bitwidths
    let mut vset = HashSet::<String>::new();
    collect_vars_int(&ie, &mut vset);
    let mut vars: Vec<String> = vset.into_iter().collect();
    vars.sort();

    // owner bitwidth
    let owner_bw = *max_bit_map
        .get(owner)
        .unwrap_or_else(|| panic!("missing bitwidth for owner '{}'", owner));
    let owner_max = (1_i64 << owner_bw) - 1;

    // precompute each var's domain 0..2^bw-1
    let domains: Vec<Vec<i64>> = vars.iter().map(|v| {
        let bw = *max_bit_map
            .get(v)
            .unwrap_or_else(|| panic!("missing bitwidth for int var '{}'", v));
        let top = (1_i64 << bw) - 1;
        (0..=top).collect()
    }).collect();

    // 3) iterate cartesian product
    let mut clauses: Vec<Box<Expression>> = Vec::new();
    let mut idx = vec![0usize; vars.len()];

    'outer: loop {
        // build env for this point
        let mut env: HashMap<String, i64> = HashMap::with_capacity(vars.len());
        for (i, v) in vars.iter().enumerate() {
            env.insert(v.clone(), domains[i][idx[i]]);
        }

        // evaluate expression
        if let Some(res) = eval_int(&ie, &env) {
            if 0 <= res && res <= owner_max {
                // antecedent: ∧ (v == env[v])   (unprimed)
                let mut ants: Vec<Box<Expression>> = Vec::with_capacity(vars.len());
                for (i, v) in vars.iter().enumerate() {
                    let bw = *max_bit_map.get(v).unwrap();
                    ants.push(Box::new(build_bitblasted_equality(v, domains[i][idx[i]], bw, false)));
                }
                let antecedent = if ants.len() == 1 {
                    *ants.pop().unwrap()
                } else {
                    Expression::MAnd(ants)
                };

                // consequent: owner' == res  (primed)
                let consequent = build_bitblasted_equality(owner, res, owner_bw, true);

                // implication
                clauses.push(Box::new(Expression::Implies(
                    Box::new(antecedent),
                    Box::new(consequent),
                )));
            }
        }
        // advance product indices
        let mut k = vars.len();
        while k > 0 {
            k -= 1;
            idx[k] += 1;
            if idx[k] < domains[k].len() { break; }
            idx[k] = 0;
            if k == 0 {
                break 'outer;
            }
        }
        if vars.is_empty() { break; }
    }

    // Big AND of all implications (or True if none)
    if clauses.is_empty() {
        Expression::True
    } else if clauses.len() == 1 {
        *clauses.pop().unwrap()
    } else {
        Expression::MAnd(clauses)
    }
}





































fn base_name(name: &str) -> &str {
    let name = name.trim_end_matches('\'');
    if let Some(i) = name.find('[') { &name[..i] } else { name }
}
// Recursively check if expr mentions any predicate atom
fn contains_predicate_atom(e: &Expression, preds: &HashSet<String>) -> bool {
    use Expression::*;
    match e {
        Literal(Lit::Atom(s)) | Literal(Lit::NegAtom(s)) => {
            preds.contains(base_name(s))
        }
        True | False => false,
        Neg(x)       => contains_predicate_atom(x, preds),
        And(a,b) | Or(a,b) | Implies(a,b) | Iff(a,b) =>
            contains_predicate_atom(a, preds) || contains_predicate_atom(b, preds),
        MAnd(xs) | MOr(xs) =>
            xs.iter().any(|x| contains_predicate_atom(x, preds)),
        // if temporals can appear here:
        G(x) | F(x) | X(x) => contains_predicate_atom(x, preds),
        U(a,b) | R(a,b)    => contains_predicate_atom(a, preds) || contains_predicate_atom(b, preds),
    }
}


pub fn subst_predicates_fixpoint(e: &Expression, predmap: &std::collections::HashMap<String, Expression>) -> Expression {
    const MAX_ROUNDS: usize = 64; // safety cap for accidental cycles
    let mut cur = e.clone();
    for _ in 0..MAX_ROUNDS {
        let next = subst_predicates(&cur, predmap);
        if next == cur {
            return cur;
        }
        cur = next;
    }
    panic!("Predicate substitution did not converge (possible cyclic predicates).");
}

pub fn subst_predicates(e: &Expression, predmap: &PredMap) -> Expression {
    use Expression::*;
    use Lit::*;

    match e {
        Literal(Atom(name)) => {
            if let Some(body) = predmap.get(name) {
                body.clone()
            } else {
                e.clone()
            }
        }
        Literal(NegAtom(name)) => {
            if let Some(body) = predmap.get(name) {
                Neg(Box::new(body.clone()))
            } else {
                e.clone()
            }
        }

        True | False => e.clone(),
        Neg(x)       => Neg(Box::new(subst_predicates(x, predmap))),
        And(a,b)     => And(Box::new(subst_predicates(a, predmap)), Box::new(subst_predicates(b, predmap))),
        Or(a,b)      => Or(Box::new(subst_predicates(a, predmap)),  Box::new(subst_predicates(b, predmap))),
        Implies(a,b) => Implies(Box::new(subst_predicates(a, predmap)), Box::new(subst_predicates(b, predmap))),
        Iff(a,b)     => Iff(Box::new(subst_predicates(a, predmap)),     Box::new(subst_predicates(b, predmap))),
        MAnd(xs)     => MAnd(xs.iter().map(|x| Box::new(subst_predicates(x, predmap))).collect()),
        MOr(xs)      => MOr(xs.iter().map(|x| Box::new(subst_predicates(x, predmap))).collect()),
        _ => todo!(),
    }
}

/// Stamp ONLY atoms with `[path][t]`; numbers/TRUE/FALSE are left as-is.
/// No temporals assumed (use your unroller before this if needed).
pub fn stamp_expr_at_time_with_path(e: &Expression, path: &str, t: usize) -> Expression {
    use Expression::*;
    use Lit::*;

    match e {
        Literal(Atom(name)) => {
            if is_int_literal(name) || is_bool_word(name) { e.clone() }
            else { Literal(Atom(stamp_name_with(path, t, name))) }
        }
        Literal(NegAtom(name)) => {
            if is_int_literal(name) || is_bool_word(name) { e.clone() }
            else { Literal(NegAtom(stamp_name_with(path, t, name))) }
        }

        True | False => e.clone(),
        Neg(x)       => Neg(Box::new(stamp_expr_at_time_with_path(x, path, t))),
        And(a,b)     => And(Box::new(stamp_expr_at_time_with_path(a, path, t)),
                            Box::new(stamp_expr_at_time_with_path(b, path, t))),
        Or(a,b)      => Or(Box::new(stamp_expr_at_time_with_path(a, path, t)),
                           Box::new(stamp_expr_at_time_with_path(b, path, t))),
        Implies(a,b) => Implies(Box::new(stamp_expr_at_time_with_path(a, path, t)),
                                Box::new(stamp_expr_at_time_with_path(b, path, t))),
        Iff(a,b)     => Iff(Box::new(stamp_expr_at_time_with_path(a, path, t)),
                            Box::new(stamp_expr_at_time_with_path(b, path, t))),
        MAnd(xs)     => MAnd(xs.iter().map(|x| Box::new(stamp_expr_at_time_with_path(x, path, t))).collect()),
        MOr(xs)      => MOr(xs.iter().map(|x| Box::new(stamp_expr_at_time_with_path(x, path, t))).collect()),
        _            => todo!(),
    }
}

pub fn fast_next_expr_from_return<'ctx>(
    ret: &ReturnType<'ctx>,
    var_name: &str,
    max_bit_map: &HashMap<String, usize>,
) -> Option<Expression> {
    // current and next variable atoms
    let curr_var = Expression::Literal(Lit::Atom(var_name.to_string()));
    let next_var = Expression::Literal(Lit::Atom(format!("{}'", var_name)));

    match ret {
        // ---- BOOL domain ----
        ReturnType::Bool(vals) if vals.is_empty() => {
            None
        }
        ReturnType::Bool(vals) if vals.len() == 1 => {
            let next_var = Expression::Literal(Lit::Atom(format!("{}'", var_name)));
            Some(if vals[0] { next_var } else { Expression::Neg(Box::new(next_var)) })
        }
        ReturnType::Bool(vals) => {
            // nondet Bool: e.g. {TRUE,FALSE} => var' ∨ ¬var'
            let next_var = Expression::Literal(Lit::Atom(format!("{}'", var_name)));
            let mut disj = Vec::new();
            if vals.iter().any(|&b| b)     { disj.push(Box::new(next_var.clone())); }
            if vals.iter().any(|&b| !b)    { disj.push(Box::new(Expression::Neg(Box::new(next_var)))); }
            Some(match disj.len() { 
                0 => Expression::False, 1 => *disj.into_iter().next().unwrap(), _ => Expression::MOr(disj) })
        }

        // ---- INT domain ----
        ReturnType::Int(vals) if vals.is_empty() => {
            None
        }
        ReturnType::Int(vals) if vals.len() == 1 => {
            let bw = *max_bit_map.get(var_name).expect("missing bitwidth");
            Some(build_bitblasted_equality(var_name, vals[0], bw, true))
        }
        ReturnType::Int(vals) => {
            let bw = *max_bit_map.get(var_name).expect("missing bitwidth");
            let mut uniq = vals.clone();
            uniq.sort_unstable();
            uniq.dedup();
            let mut arms = Vec::with_capacity(uniq.len());
            for &v in &uniq {
                arms.push(Box::new(build_bitblasted_equality(var_name, v, bw, true)));
            }
            Some(match arms.len() { 0 => Expression::False, 1 => *arms.into_iter().next().unwrap(), _ => Expression::MOr(arms) })
        }

        // ---- DynAst fast paths ----
        ReturnType::DynAst(ast) => {
            // Bool literal
            if let Some(b) = ast.as_bool().and_then(|b| b.as_bool()) {
                let next_var = Expression::Literal(Lit::Atom(format!("{}'", var_name)));
                return Some(if b { next_var } else { Expression::Neg(Box::new(next_var)) });
            }
            // Int literal
            if let Some(val) = ast.as_int().and_then(|i| i.as_i64()) {
                let bw = *max_bit_map.get(var_name).expect("missing bitwidth");
                return Some(build_bitblasted_equality(var_name, val, bw, true));
            }
            // Bare symbol like low!2
            if ast.children().is_empty() {
                let base = clean_var_name(&ast.decl().name().to_string(), false);
                let lhs = Expression::Literal(Lit::Atom(format!("{}'", base)));
                let rhs = Expression::Literal(Lit::Atom(base));
                return Some(Expression::Iff(Box::new(lhs), Box::new(rhs)));
            }
            None
        }

        // ---- other domains ----
        _ => None,
    }
}

pub fn fast_init_expr_from_return<'ctx>(
    ret: &ReturnType<'ctx>,
    var_name: &str,
    max_bit_map: &HashMap<String, usize>,
) -> Option<Expression> {
    // current and next variable atoms
    let curr_var = Expression::Literal(Lit::Atom(var_name.to_string()));
    // let next_var = Expression::Literal(Lit::Atom(format!("{}'", var_name)));

    match ret {
        // ---- BOOL domain ----
        ReturnType::Bool(vals) if vals.is_empty() => {
            None
        }
        ReturnType::Bool(vals) if vals.len() == 1 => {
            Some(if vals[0] { curr_var } else { Expression::Neg(Box::new(curr_var)) })
        }
        ReturnType::Bool(vals) => {
            // nondet Bool: e.g. {TRUE,FALSE} => var' ∨ ¬var'
            let mut disj = Vec::new();
            if vals.iter().any(|&b| b)     { disj.push(Box::new(curr_var.clone())); }
            if vals.iter().any(|&b| !b)    { disj.push(Box::new(Expression::Neg(Box::new(curr_var)))); }
            Some(match disj.len() { 
                0 => Expression::False, 1 => *disj.into_iter().next().unwrap(), _ => Expression::MOr(disj) })
        }

        // ---- INT domain ----
        ReturnType::Int(vals) if vals.is_empty() => {
            None
        }
        ReturnType::Int(vals) if vals.len() == 1 => {
            let bw = *max_bit_map.get(var_name).expect("missing bitwidth");
            Some(build_bitblasted_equality(var_name, vals[0], bw, true))
        }
        ReturnType::Int(vals) => {
            let bw = *max_bit_map.get(var_name).expect("missing bitwidth");
            let mut uniq = vals.clone();
            uniq.sort_unstable();
            uniq.dedup();
            let mut arms = Vec::with_capacity(uniq.len());
            for &v in &uniq {
                arms.push(Box::new(build_bitblasted_equality(var_name, v, bw, true)));
            }
            Some(match arms.len() { 0 => Expression::False, 1 => *arms.into_iter().next().unwrap(), _ => Expression::MOr(arms) })
        }

        // ---- other domains ----
        _ => None,
    }
}

/// Convert a boolean `Expression` (True/False) into a literal of `next_var`.
/// - If `next_expr` is True  → Atom(next_var)
/// - If `next_expr` is False → NegAtom(next_var)
/// - Otherwise               → just return `next_expr.clone()`
fn bool_to_var_literal(v: &String, next_expr: &Expression) -> Expression {
    match next_expr {
        Expression::True => {
            // if let Expression::Literal(Lit::Atom(v)) = next_var {
                Expression::Literal(Lit::Atom(v.clone()))
            // } else {
                // next_expr.clone()
            // }
        }
        Expression::False => {
            // if let Expression::Literal(Lit::Atom(v)) = next_var {
                Expression::Literal(Lit::NegAtom(v.clone()))
            // } else {
                // next_expr.clone()
            // }
        }
        _ => next_expr.clone(),
    }
}

// Helper: parse the quantifier String -> Quant
fn parse_quant(s: &str) -> Quant {
    match s {
        // accept a few common spellings
        "A" | "∀" | "Forall" | "FORALL" | "forall" => Quant::Forall,
        "E" | "∃" | "Exists" | "EXISTS" | "exists" => Quant::Exists,
        other => panic!("Unknown quantifier: {other}"),
    }
}

/// Convert any ReturnType into a Dynamic Bool constraint.
/// Errors if the domain is empty (e.g., Int([]) / Bool([])).
fn ret_to_dynamic_result<'ctx>(
    ctx:   &'ctx z3::Context,
    env:   &SMVEnv<'ctx>,
    state: &EnvState<'ctx>,
    var_name: &str,
    mut ret: ReturnType<'ctx>,
) -> Result<Dynamic<'ctx>, String> {
    match ret {
        ReturnType::Int(ref v)  if v.is_empty() => return Err("empty Int domain".into()),
        ReturnType::Bool(ref v) if v.is_empty() => return Err("empty Bool domain".into()),
        ReturnType::BVector(_)                  => return Err("BVector not supported".into()),
        _ => {}
    }
    Ok(ret.into_dynamic(ctx, env, state, var_name))
}

/// Replace all occurrences of `[X]` with `_X`, where X is any string of
/// letters, digits, or underscores.
pub fn substitute_brackets(formula: &str) -> String {
    // This regex captures the content inside [ ... ]
    let re = Regex::new(r"\[([^\]]+)\]").unwrap();

    // For each match, prepend an underscore to the inner content
    re.replace_all(formula, |caps: &regex::Captures| {
        format!("_{}", &caps[1])
    })
    .into_owned()
}

/// Quick check if a formula is async
pub fn is_ahltl(formula: &str) -> bool {
    // Short-form: [AE] <spaces> (optional identifier) <optional spaces> "."
    // Matches: "E t .", "A idx .", and also "E .", "A ."
    let short = Regex::new(r"\b[AE]\s+(?:[A-Za-z_]\w*\s*)?\.").unwrap();

    // If the short-form token is immediately preceded by "Forall" or "Exists"
    // (with only whitespace or '(' between), then it's part of long-form; skip it.
    let left_ctx = Regex::new(r"(?:^|[\s(])(?:Forall|Exists)\s*$").unwrap();

    for m in short.find_iter(formula) {
        let prefix = &formula[..m.start()];
        if left_ctx.is_match(prefix) {
            continue; // this "A/E ... ." belongs to long-form quantifier
        }
        return true; // genuine short-form found -> A-HLTL
    }
    false
}


// A Dynamic is a symbol iff it has no children.
fn is_symbol(node: &Dynamic) -> bool {
    node.children().is_empty()
}

// Extract boolean constant if the node *is* a literal true/false.
fn bool_const_of(node: &Dynamic) -> Option<bool> {
    node.as_bool()?.as_bool()
}

// Only create an Atom from a true symbol.
fn atom_from_symbol(node: &Dynamic, is_primed: bool) -> Expression {
    let name = node.decl().name().to_string();
    let cleaned = clean_var_name(&name, is_primed);
    match cleaned.as_str() {
        "true"  => Expression::True,
        "false" => Expression::False,
        _       => Expression::Literal(Lit::Atom(cleaned)),
    }
}





// Helper (put it once near your other utils)
fn negate_expr(e: Expression) -> Expression {
    use expressions::{Expression, Literal as Lit};
    match e {
        Expression::Literal(Lit::Atom(s))    => Expression::Literal(Lit::NegAtom(s)),
        Expression::Literal(Lit::NegAtom(s)) => Expression::Literal(Lit::Atom(s)),
        Expression::True                     => Expression::False,
        Expression::False                    => Expression::True,
        Expression::Neg(inner)               => *inner, // ¬(¬φ) → φ
        other                                => Expression::Neg(Box::new(other)),
    }
}

fn encode_cmp_dyn(
    op: &str,
    left: &Dynamic,
    right: &Dynamic,
    is_primed: bool,
    max_bit_map: &HashMap<String, usize>,
    var_name_hint: &str, // if you have a preferred variable context, else pass ""
) -> Expression {

    if op == "="
        && left.get_sort().kind() == SortKind::Bool
        && right.get_sort().kind() == SortKind::Bool
    {
        let l = dyn_to_expr(var_name_hint, &Dynamic::from_ast(left),  is_primed, max_bit_map);
        let r = dyn_to_expr(var_name_hint, &Dynamic::from_ast(right), is_primed, max_bit_map);
        return Expression::Iff(Box::new(l), Box::new(r));
    }

    // println!("Left  (to_string): {}", left.to_string());
    // println!("Right (to_string): {}", right.to_string());


    // 1) Pull out ints / vars if possible
    let l_sort = left.get_sort().kind();
    let r_sort = right.get_sort().kind();

    let l_int = int_literal_of(left);
    let r_int = int_literal_of(right);

    // Only try to read a “variable” if it's not a literal integer
    let l_var = if l_int.is_none() { var_base_of_dyn(left) } else { None };
    let r_var = if r_int.is_none() { var_base_of_dyn(right) } else { None };

    // Debug: print the whole situation so you can see misclassifications
    // eprintln!(
    //     "[cmp debug] op={}  l_sort={:?} r_sort={:?}  l_int={:?} r_int={:?}  l_var={:?} r_var={:?}",
    //     op, l_sort, r_sort, l_int, r_int, l_var, r_var
    // );
    // println!("VAR: {:?}", l_var);
    // println!("INT: {:?}", r_int);

    // Helper to fetch bitwidth (panics if missing)
    let bw_of = |v: &str| -> usize {
        let key = unprimed_base(v);
        *max_bit_map.get(&key).expect(&format!("missing bitwidth for '{}'", key))
    };

    match (l_int, l_var.as_deref(), r_int, r_var.as_deref()) {
        // var ◦ const
        (None, Some(v), Some(c), None) => {
            let bw = bw_of(v);
            let (min, max) = unsigned_domain(bw);
            // clamp c into domain for range limits
            let c = c.clamp(min, max);

            match op {
                "="  => build_bitblasted_equality(v, c, bw, is_primed),
                "<"  => {
                    if c <= min { Expression::False } else {
                        build_or_eqs_to_values(v, min..=c-1, bw, is_primed)
                    }
                }
                "<=" => build_or_eqs_to_values(v, min..=c,   bw, is_primed),
                ">"  => {
                    if c >= max { Expression::False } else {
                        build_or_eqs_to_values(v, c+1..=max, bw, is_primed)
                    }
                }
                ">=" => build_or_eqs_to_values(v, c..=max,   bw, is_primed),
                _    => panic!("unknown op {}", op),
            }
        }

        // const ◦ var  -> flip sides/op and reuse
        (Some(c), None, None, Some(v)) => {
            let flipped = match op {
                "<"  => ">",  "<=" => ">=",  ">" => "<",  ">=" => "<=", "=" => "=", _ => op
            };
            encode_cmp_dyn(flipped, right, left, is_primed, max_bit_map, var_name_hint)
        }

        // const ◦ const  -> decide truth immediately
        (Some(a), None, Some(b), None) => {
            let holds = match op {
                "="  => a == b,
                "<"  => a <  b,
                "<=" => a <= b,
                ">"  => a >  b,
                ">=" => a >= b,
                _    => false,
            };
            if holds { Expression::True } else { Expression::False }
        }

        // var ◦ var  (complete enumeration; can be large!)
        (None, Some(v1), None, Some(v2)) => {
            let bw1 = bw_of(v1);
            let bw2 = bw_of(v2);
            encode_var_rel_var(op, v1, bw1, is_primed, v2, bw2, is_primed)
        }

        // fallback: one/both sides not recognized as int-or-var; translate structurally
        _ => {
            // If you want a structural fallback, convert each side into Expression and drop an Iff/compare.
            // For "=", a reasonable fallback:
            let l = dyn_to_expr(var_name_hint, &Dynamic::from_ast(left),  is_primed, max_bit_map);
            let r = dyn_to_expr(var_name_hint, &Dynamic::from_ast(right), is_primed, max_bit_map);
            match op {
                "="  => Expression::Iff(Box::new(l), Box::new(r)),
                "<" | "<=" | ">" | ">=" => {
                    eprintln!(
            "Non-integer comparison fallback not supported!\n  op: {}\n  left: {:?}\n  right: {:?}\n",
            op,
            l,
            r,
            // l.get_sort().kind(),
            // r.get_sort().kind(),
            );
            panic!("Non-integer comparison fallback not supported for op {}", op);
                }
                _ => panic!("unknown op {}", op),
            }
        }
    }
}

fn is_int_literal(s: &str) -> bool {
    let s = s.trim();
    if s.is_empty() { return false; }
    let rest = if s.starts_with('+') || s.starts_with('-') { &s[1..] } else { s };
    !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit())
}

fn is_bool_word(s: &str) -> bool {
    s.eq_ignore_ascii_case("true") || s.eq_ignore_ascii_case("false")
}

/// Does the name already end with a time like `[12]`?
fn has_trailing_time(name: &str) -> bool {
    if !name.ends_with(']') { return false; }
    if let Some(i) = name.rfind('[') {
        name[i+1..name.len()-1].chars().all(|c| c.is_ascii_digit())
    } else {
        false
    }
}

fn stamp_name_once(name: &str, t: usize) -> String {
    if has_trailing_time(name) {
        name.to_string()
    } else {
        format!("{name}[{t}]")
    }
}

/// name -> name[t], assuming it doesn't already have a trailing [k].
fn stamp_name(name: &str, t: usize) -> String {
    format!("{name}[{t}]")
}

fn stamp_name_with(path: &str, t: usize, base: &str) -> String {
    // base -> base[path][t]
    format!("{base}[{path}][{t}]")
}



/// Is this Dynamic an integer literal (e.g., `1`, `-3`)?
fn is_int_lit(d: &Dynamic) -> bool {
    d.as_int().and_then(|i| i.as_i64()).is_some()
}

fn int_literal_of(d: &z3::ast::Dynamic) -> Option<i64> {
    if let Some(i) = d.as_int() {
        if let Some(v) = i.as_i64() {
            return Some(v);
        }
        // fallback parse in case Z3 won’t give as_i64 directly
        if let Ok(v) = i.to_string().parse::<i64>() {
            return Some(v);
        }
    }
    None
}

fn is_bool_lit(d: &z3::ast::Dynamic) -> bool {
    d.get_sort().kind() == z3::SortKind::Bool &&
    d.as_bool().and_then(|b| b.as_bool()).is_some()
}

fn var_base_of_dyn(d: &z3::ast::Dynamic) -> Option<String> {
    // exclude literals first (prevents “1” from being treated as a var)
    if int_literal_of(d).is_some() || is_bool_lit(d) {
        return None;
    }
    if d.children().is_empty() {
        let sym = d.decl().name().to_string();          // e.g., "PC!1"
        return Some(clean_var_name(&sym, false));
    }
    None
}


/// Try left, then right. Returns Some(base) or None if neither looks like a var.
fn var_name_hint_from_children(left: &Dynamic, right: &Dynamic) -> Option<String> {
    var_base_of_dyn(left).or_else(|| var_base_of_dyn(right))
}

fn unprimed_base(sym: &str) -> String {
    sym.trim_end_matches('\'').to_string()
}

fn var_base_of(d: &Dynamic, is_primed: bool) -> Option<String> {
    if d.children().is_empty() {
        let sym = d.decl().name().to_string();
        Some(clean_var_name(&sym, false /* get base unprimed */))
    } else {
        None
    }
}

// Signed two's-complement domain for given bitwidth.
fn signed_domain(bitwidth: usize) -> (i64, i64) {
    assert!(bitwidth > 0 && bitwidth <= 63, "bitwidth in 1..=63 expected");
    let min = - (1i64 << (bitwidth - 1));
    let max =    (1i64 << (bitwidth - 1)) - 1;
    (min, max)
}

fn unsigned_domain(bitwidth: usize) -> (i64, i64) {
    assert!(bitwidth > 0 && bitwidth <= 62, "bitwidth in 1..=62 expected");
    let max = (1i64 << bitwidth) - 1;
    (0, max)
}

// Build OR over equalities var == c for all c in iterable
fn build_or_eqs_to_values<I: IntoIterator<Item = i64>>(
    var_name: &str,
    values: I,
    bitwidth: usize,
    is_primed: bool,
) -> Expression {
    let mut disj = Vec::new();
    for c in values {
        disj.push(Box::new(build_bitblasted_equality(var_name, c, bitwidth, is_primed)));
    }
    if disj.is_empty() {
        Expression::False
    } else if disj.len() == 1 {
        *disj.into_iter().next().unwrap()
    } else {
        Expression::MOr(disj)
    }
}

// Full enumeration for var ◦ var (potentially large!)
fn encode_var_rel_var(
    op: &str,
    v1: &str, bw1: usize, p1: bool,
    v2: &str, bw2: usize, p2: bool,
) -> Expression {
    let (min1, max1) = signed_domain(bw1);
    let (min2, max2) = signed_domain(bw2);

    // For equality we can optimize: single AND of per-bit IFFs
    if op == "=" && v1 == v2 && bw1 == bw2 && p1 == p2 {
        // same signal, same time => tautology
        return Expression::True;
    }
    if op == "=" {
        let mut lanes = Vec::with_capacity(bw1.min(bw2));
        for i in 0..bw1.min(bw2) {
            let a = Expression::Literal(Lit::Atom(format!("{}_{}", v1, i) + if p1 { "'" } else { "" }));
            let b = Expression::Literal(Lit::Atom(format!("{}_{}", v2, i) + if p2 { "'" } else { "" }));
            lanes.push(Box::new(Expression::Iff(Box::new(a), Box::new(b))));
        }
        return Expression::MAnd(lanes);
    }

    // General case: OR over all pairs (c1, c2) satisfying c1 op c2
    //   (v1 == c1) ∧ (v2 == c2)
    let mut big = Vec::new();
    for c1 in min1..=max1 {
        // derive the allowed c2 range depending on op and c1
        let range: Box<dyn Iterator<Item=i64>> = match op {
            "<"  => Box::new(min2..=c1-1),
            "<=" => Box::new(min2..=c1),
            ">"  => Box::new(c1+1..=max2),
            ">=" => Box::new(c1..=max2),
            _    => Box::new(min2..=max2), // shouldn't happen
        };
        let left  = build_bitblasted_equality(v1, c1, bw1, p1);
        let right = build_or_eqs_to_values(v2, range, bw2, p2);
        big.push(Box::new(Expression::And(Box::new(left), Box::new(right))));
    }
    if big.is_empty() {
        Expression::False
    } else if big.len() == 1 {
        *big.into_iter().next().unwrap()
    } else {
        Expression::MOr(big)
    }
}


fn bit_atom(var: &str, i: usize, primed: bool) -> Expression {
    let name = if primed {
        format!("{}_{}'", var, i)
    } else {
        format!("{}_{}", var, i)
    };
    Expression::Literal(Lit::Atom(name))
}

/// Build (var_{n-1} <-> var_{n-1}') /\ ... /\ (var_0 <-> var_0')
pub fn build_bitblasted_self_eq(var_name: &str, bitwidth: usize) -> Expression {
    let mut lanes = Vec::with_capacity(bitwidth);
    for i in (0..bitwidth).rev() {
        let a = bit_atom(var_name, i, false);
        let b = bit_atom(var_name, i, true);
        lanes.push(Box::new(Expression::Iff(Box::new(a), Box::new(b))));
    }
    Expression::MAnd(lanes)
}


/// Returns Some(true) / Some(false) iff `node` is a boolean **constant**,
/// or an equality to a single boolean constant (e.g., `b == true` / `b == false`).
pub fn bool_singleton(node: &Dynamic) -> Option<bool> {
    // quick path: literal true/false
    if let Some(b_ast) = node.as_bool() {
        if let Some(v) = b_ast.as_bool() {
            return Some(v);
        }
    }

    // singleton encoded as equality to a bool constant
    if node.get_sort().kind() == SortKind::Bool && node.num_children() == 2 {
        // try to detect "=" (best-effort via name; decl kind isn’t exposed directly)
        if node.decl().name().to_string() == "=" {
            let kids = node.children();
            // check if either side is a bool constant
            if let Some(v) = kids[0].as_bool().and_then(|b| b.as_bool()) {
                return Some(v);
            }
            if let Some(v) = kids[1].as_bool().and_then(|b| b.as_bool()) {
                return Some(v);
            }
        }
    }

    None
}

/// Returns Some(c) iff `node` is a **single integer equality** `x == c`.
/// (Note: this is still a Bool-typed formula; we’re extracting the singleton value `c`.)
pub fn int_singleton(node: &Dynamic) -> Option<i64> {
    if node.get_sort().kind() != SortKind::Bool || node.num_children() != 2 {
        return None;
    }
    if node.decl().name().to_string() != "=" {
        return None;
    }
    let kids = node.children();
    // if either side is an Int numeral, return it
    if let Some(c) = kids[0].as_int().and_then(|i| i.as_i64()) {
        return Some(c);
    }
    if let Some(c) = kids[1].as_int().and_then(|i| i.as_i64()) {
        return Some(c);
    }
    None
}

/// Backward-compatible helpers that now also recognize the singleton-encoded cases.
pub fn is_dyn_true(node: &Dynamic) -> bool {
    bool_singleton(node) == Some(true)
}
pub fn is_dyn_false(node: &Dynamic) -> bool {
    bool_singleton(node) == Some(false)
}



pub fn clean_var_name(var_name: &str, is_primed: bool) -> String {
    // 1. Remove everything after '!' if present
    let mut cleaned = var_name
        .find(|c: char| c == '!')
        .map(|idx| var_name[..idx].to_string())
        .unwrap_or_else(|| var_name.to_string());

    // 2. Strip specific suffixes
    if let Some(stripped) = cleaned.strip_suffix("_0_bound") {
        cleaned = stripped.to_string();
    } else if let Some(stripped) = cleaned.strip_suffix("_0_init") {
        cleaned = stripped.to_string();
    } 
    // else if let Some(stripped) = cleaned.strip_suffix("_0") {
    //     cleaned = stripped.to_string();
    // } else if let Some(stripped) = cleaned.strip_suffix("_1") {
    //     // Special case: replace `_1` with a prime
    //     cleaned = format!("{}'", stripped);
    // }
    if is_primed {
        cleaned.push('\'');
    }

    cleaned
}

fn is_bool(node: &Dynamic) -> bool {
    node.get_sort().kind() == z3::SortKind::Bool
}

// HELPER: bit-blast a variable with expression (var_name = val)
fn build_bitblasted_equality(var_name: &str, val: i64, bitwidth: usize, is_primed: bool) -> Expression {
    // Compute the minimum number of bits needed to represent `val` in two's complement
    // println!("build_bitblasted: {:?}, {:?}, {:?}", var_name, val, bitwidth);

    let needed_bits = if val >= 0 {
        64 - val.leading_zeros()
    } else {
        64 - (!val).leading_zeros() + 1
    };

    if (needed_bits as usize) > bitwidth {
        eprintln!(
            "Error in build_bitblasted_equality(): bitwidth {} is too small to represent value {} for variable '{}'",
            bitwidth, val, var_name
        );
        std::process::exit(1);
    }
    
    let mut bits = vec![];
    for i in (0..bitwidth).rev() {
        let mut bit_name = format!("{}_{}", var_name, i);
        if is_primed {
            bit_name.push('\'');
        }
        let expected = (val >> i) & 1;
        let bit_expr = if expected == 1 {
            Expression::Literal(Lit::Atom(bit_name))
        } else {
            Expression::Neg(Box::new(Expression::Literal(Lit::Atom(bit_name))))
        };
        bits.push(Box::new(bit_expr));
    }

    Expression::MAnd(bits)
}

pub fn replace_last_occurrence(atom: &str, target: &str, replacement: &str) -> String {
    if let Some(idx) = atom.rfind(target) {
        let mut result = String::with_capacity(atom.len() + replacement.len() - target.len());
        result.push_str(&atom[..idx]);
        result.push_str(replacement);
        result.push_str(&atom[idx + target.len()..]);
        result
    } else {
        atom.to_string()
    }
}

















// // Update: conform with new defined formula IR
// // quantifiers: place to store quantifiers gotten from formula
// // formula: the formula to parse
// // complete_bit_map: hash map that stores (variable: max_bit_order) for bit-blasting
// fn hq_parser(mut quantifiers: Vec<(String, String)>, formula: String, debug: bool, complete_bit_map: HashMap<String, i32>) -> (String, Vec<(String, String)>) {

//     let quantifier_pattern = Regex::new(r"(Forall|Exists)\s+([A-Za-z_][A-Za-z0-9_]*) \.").unwrap();

//     // let mut quantifiers: Vec<(String, String)> = Vec::new();
//     let mut remaining_formula = formula.to_string();
    
//     for cap in quantifier_pattern.captures_iter(&formula.clone()) {
//         if let (Some(quantifier), Some(variable)) = (cap.get(1), cap.get(2)) {
//             quantifiers.push((quantifier.as_str().to_string(), variable.as_str().to_string()));
//         }
//         remaining_formula = quantifier_pattern.replace(&remaining_formula, "").to_string();
//     }
//     let pattern = Regex::new(r"\[(.*?)\]").unwrap();

//     // let modified_formula = pattern.replace_all(&remaining_formula, "_$1");

//     if debug {
//         println!("Quantifiers and Variables: {:?}", quantifiers); 
//         // println!("Remaining Formula: {}", remaining_formula.trim());
//         // println!("Modified Formula: {}", modified_formula);
//     }

//     // patterns of the numerical values
//     let re = Regex::new(
//     r#"\(\s*(\w+(?:\[\w+\])*)\[(\w+)\]\s*=\s*(\d+|\w+(?:\[\w+\])*\[(\w+)\])\s*\)"#
// ).unwrap();
//     // let re = Regex::new(r#"\*\s*(\w+(?:\[\w+\])*)\[(\w+)\]\s*=\s*(\d+|\w+(?:\[\w+\])*\[(\w+)\])\s*\*"#).unwrap();
//     if debug {
//         // Function to process and print matches
//         for captures in re.captures_iter(&remaining_formula.clone()) {
//             // Extract matched groups
//             let var1 = captures.get(1).map_or("", |m| m.as_str());
//             let bracket1 = captures.get(2).map_or("", |m| m.as_str());
//             let rhs = captures.get(3).map_or("", |m| m.as_str());

//             // is rhs a variable or an integer
//             if let Some(int_match) = captures.get(3).and_then(|m| m.as_str().parse::<i32>().ok()) {
//                 println!("Pattern: var = int");
//                 println!("var = {}", var1);
//                 println!("bracket = {}", bracket1);
//                 println!("value = {}", int_match);
//             } else if let Some(var_match) = captures.get(3) {
//                 let var2 = var_match.as_str();
//                 let bracket2 = captures.get(4).map_or("", |m| m.as_str());
//                 println!("Pattern: var = var");
//                 println!("var1 = {}", var1);
//                 println!("bracket1 = {}", bracket1);
//                 let mut var3 : &str = "";
//                 if let Some(last_open_bracket_idx) = var2.rfind('[') {
//                     // Remove the substring from the last '[' to the end
//                     var3 = &var2[..last_open_bracket_idx]; }
//                 println!("var2 = {}", var3);
//                 println!("bracket2 = {}", bracket2);
//             }
//             println!();
//         }
//     }

//     let mut replacements = Vec::new();

//     let binding = remaining_formula.clone();
//     // Function to process matches and store replacements
//     for captures in re.captures_iter(&binding) {
//         // Extract matched groups
//         let var1 = captures.get(1).map_or("", |m| m.as_str());
//         let bracket1 = captures.get(2).map_or("", |m| m.as_str());
//         let rhs = captures.get(3).map_or("", |m| m.as_str());
        
//         // pattern : var = int
//         let new_pattern = if let Some(_) = rhs.parse::<i32>().ok() {
//             let max_bit = *complete_bit_map.get(var1).unwrap_or(&0);
//             if max_bit == 0 {
//                 panic!("Variable not found in bit map!");
//             }
//             // println!("MAX_BIT: {}", max_bit);
//             manipulate_pattern(max_bit, var1, bracket1, rhs, None)
//         // pattern : var = var
//         } else {
//             // println!("RHS: {}", rhs);
//             let mut var2 : &str = "";
//             if let Some(last_open_bracket_idx) = rhs.rfind('[') {
//                 // Remove the substring from the last '[' to the end
//                 var2 = &rhs[..last_open_bracket_idx];

//             }
//             // println!("RHS_change: {}", var2);
//             // let var2 = rhs;
//             let bracket2 = captures.get(4).map_or("", |m| m.as_str());
//             // find max of each var's max_bit value
//             let max_bit_1 = *complete_bit_map.get(var1).unwrap_or(&0);
//             // println!("MAX_BIT_1: {}", max_bit_1);
//             let max_bit_2 = *complete_bit_map.get(var2).unwrap_or(&0);
//             // println!("MAX_BIT_2: {}", max_bit_2);

//             if max_bit_1 != 0 && max_bit_2 != 0 {
//                 // panic!("Variable not found in bit map!");

//                 continue;
//             }
//             let max_bit = max_bit_1.max(max_bit_2);
//             manipulate_pattern(max_bit, var1, bracket1, var2, Some(bracket2))
//         };

//         // Store the original match and the new pattern
//         if let Some(matched) = captures.get(0) {
//             replacements.push((matched.as_str(), new_pattern));
//         }
//     }

//     // Replace all matches in the original string
//     for (original, replacement) in replacements {
//         if debug {
//             println!("Original: {}, Replacement: {}", original, replacement);
//         }
//         remaining_formula = remaining_formula.replace(original, &replacement);
//     }

//     // let pattern = Regex::new(r"\\d+|[a-zA-Z'_0-9\[\].]+").unwrap();
//     // PATCH
//     let replaced = remaining_formula.replace("=", "<->");
//     let mut form = replaced.clone();
//     println!("Remaining Formula: {}", form.trim());
//     // for cap in pattern.captures_iter(&remaining_formula){
//     //     // if cap has [] then it is a variable, so replace the last [thing] with _thing
//     //     let matched = cap.get(0).unwrap();
//     //     if matched.as_str().contains("[") { // its a variable
//     //         let mut variable = matched.as_str().to_owned();
//     //         variable = replace_last_occurrence(&variable, "]", "");
//     //         variable = replace_last_occurrence(&variable, "[", "_");
//     //         form = form.replace(matched.as_str(), &*variable);
//     //     }}
//     // if debug {
//     //     println!("Quantifiers and Variables: {:?}", quantifiers);
//     //     println!("Remaining Formula: {}", remaining_formula.trim());
//     //     println!("Modified Formula: {}", form);
//     //     raise_error("Completed HQ Parser",1);
//     // }

//     return (form, quantifiers);
// }
