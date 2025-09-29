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

// mod flag;
use flags::flags::parse_flags;


pub fn gen_qcir(
    files: &Vec<&str>, 
    formula_file: &String, 
    env: &SMVEnv, 
    layers: i32, 
    debug: bool, 
    semantics: &str
){

    let mut expr_vec: Vec<Box<Expression>> = vec![];
    let mut complete_bit_map : HashMap<String, i32> = HashMap::new();
    let mut init_map: HashMap<String, Vec<String>> = HashMap::new();
    // init_map_vec structure -- [(filename, init_map),...]
    let mut init_map_vec: Vec<(String, HashMap<String, Vec<String>>)> = Vec::new(); 
    let mut models: Vec<(String,String)> = Vec::new(); // all init maps in a vec

    for file in files.iter() {
        println!("parsing {}...", file);

        let mut max_bit_map: HashMap<String, usize> = HashMap::new();
        let variables = env.get_variables(); // returns &HashMap<String, Variable>

        // Build bit map: var name -> minimum bitwidth
        for (var_name, v) in variables {
            if let VarType::Int { upper: Some(max_val), .. } = v.sort {
                let bitwidth = (64 - (max_val).leading_zeros()) as usize;
                max_bit_map.insert(var_name.to_string(), bitwidth);
            }
        }

        // build initial condition
        let (states, _path_constraint) = env.generate_symbolic_path(1, Some("init"));
        let z3_constraints = env.generate_initial_constraints(&states);
        let mut init_exprs = Vec::new();
        for c in z3_constraints {
            let dyn_node = Dynamic::from_ast(&c);
            // println!("\nParsing initial condition: {}", dyn_node.to_string());
            let init_expr = dynamic_to_expression("", &dyn_node, false, &max_bit_map);
            init_exprs.push(Box::new(init_expr));
        }
        let full_init_expr = Expression::MAnd(init_exprs);

        // DEBUG
        // println!(">>> Initial Constraints as Expression:\n{:#?}", full_init_expr);

        let dummy_state = env.make_dummy_state(env.get_context());
        for (var_name, transitions_vec) in env.get_transitions() {
            // println!("Variable: {}", var_name);

            for (i, (guard_fn, update_fn)) in transitions_vec.iter().enumerate() {
                // println!("[ Transition #{} ]", i);

                // Evaluate guard and update only once
                let guard_result = guard_fn(env, env.get_context(), &dummy_state);

                let update_result = update_fn(env, env.get_context(), &dummy_state);

                // Extract Dynamic nodes from ReturnType
                let guard_node_opt = match guard_fn(env, env.get_context(), &dummy_state) {
                    ReturnType::DynAst(node) => Some(node),
                    ReturnType::Bool(ref bvec) if bvec.len() == 1 => {
                        let b = Bool::from_bool(env.get_context(), bvec[0]);
                        Some(Dynamic::from_ast(&b))
                    }
                    ReturnType::Int(ref ivec) if ivec.len() == 1 => {
                        let i = Int::from_i64(env.get_context(), ivec[0]);
                        Some(Dynamic::from_ast(&i))
                    }
                    _ => None,
                };

                let update_node_opt = match update_fn(env, env.get_context(), &dummy_state) {
                    ReturnType::DynAst(node) => Some(node),
                    ReturnType::Bool(ref bvec) if bvec.len() == 1 => {
                        let b = Bool::from_bool(env.get_context(), bvec[0]);
                        Some(Dynamic::from_ast(&b))
                    }
                    ReturnType::Int(ref ivec) if ivec.len() == 1 => {
                        let i = Int::from_i64(env.get_context(), ivec[0]);
                        Some(Dynamic::from_ast(&i))
                    }
                    _ => None,
                };

                if let (Some(guard_node), Some(update_node)) = (guard_node_opt, update_node_opt) {
                    
                    let curr = dynamic_to_expression(&var_name, &guard_node, false, &max_bit_map); // non-primed
                    let next = dynamic_to_expression(&var_name, &update_node, true, &max_bit_map); // primed

                    // DEBUG
                    // println!("\n> Guard node at {}: {:?}", i, guard_result);
                    // println!("as Expression:\n{:#?}", curr);
                    // println!("\n> Update node at {}: {:?}", i, update_result);
                    // println!("as Expression:\n{:#?}", next);

                    expr_vec.push(Box::new(Expression::Implies(Box::new(curr), Box::new(next))));
                } else {
                    println!("Skipping transition #{} for variable `{}`: guard or update is not DynAst.", i, var_name);
                }
            }
        }
        let full_trans_expr = Expression::MAnd(expr_vec.clone());
        expr_vec.clear();
        
        complete_bit_map.extend(
            max_bit_map.iter().map(|(k, v)| (k.clone(), *v as i32))
        );
        
        let new_pair = ((expression_to_string(&full_init_expr)), (expression_to_string(&full_trans_expr))); 
        models.push(new_pair);

        println!("success!");
    }
    

    // Rust genqbf
    let logger = Logger::new(false, 2);
    // let formula_file = files.pop().expect("Expected at least one input file");

    println!("FORMULA: {}", formula_file);

    let formula = get_expression(&*formula_file,debug);
    let pattern = Regex::new(r"\\d+|[a-zA-Z'_0-9\[\].]+").unwrap();
    let mut form = formula.clone();
    for cap in pattern.captures_iter(&*formula){
        // if cap has [] then it is a variable, so replace the last [thing] with _thing
        let matched = cap.get(0).unwrap();
        if matched.as_str().contains("[") { // its a variable
            let mut variable = matched.as_str().to_owned();
            variable = replace_last_occurrence(&variable, "]", "");
            variable = replace_last_occurrence(&variable, "[", "_");
            form = form.replace(matched.as_str(), &*variable);
        }
    }

    

    // TODO: update with Milad's binary tree
    let mut quantifiers: Vec<(String, String)> = Vec::new();
    let (modified_formula, quantifiers) = hq_parser(quantifiers, form.clone(), debug, complete_bit_map);
    println!("formula: {}", modified_formula);
    for (qtype, var) in &quantifiers {
        println!("{} {}", qtype, var);
    }

    fsm::legacy_unwrap(models, &modified_formula, layers, &logger, &quantifiers, &semantics.to_string());

}


// converting a z3 dynamic node to QBF expression package
pub fn dynamic_to_expression(
    var_name: &str,
    node: &Dynamic, 
    is_primed: bool, 
    max_bit_map: &HashMap<String, usize>
) -> Expression {
    let sort_kind = node.get_sort().kind();
    let decl_name = node.decl().name().to_string();

    // DEBUG
    // println!("\nSort: {:?}", node.get_sort());
    // println!("SMT-LIB: {}", node.to_string());
    // println!("Children count: {}", node.num_children());


    if sort_kind == SortKind::Bool {
        let children = node.children();

        if children.is_empty() {
            // base case
            let mut cleaned_name = decl_name
                .find(|c: char| c == '!' || c == '_')
                .map(|idx| decl_name[..idx].to_string())
                .unwrap_or_else(|| decl_name.clone());

            // TBD: is there "cleaner" variable names I can get?
            if let Some(stripped) = cleaned_name.strip_suffix("_0_init") {
                cleaned_name = stripped.to_string();
            } else if let Some(stripped) = cleaned_name.strip_suffix("_0") {
                cleaned_name = stripped.to_string();
            } else if let Some(stripped) = cleaned_name.strip_suffix("_1") {
                cleaned_name = format!("{}'", stripped);
            }

            if is_primed {
                cleaned_name.push('\'');
            }

            return match cleaned_name.as_str() {
                "true"  => Expression::True,
                "false" => Expression::False,
                _       => Expression::Literal(Literal::Atom(cleaned_name)),
            };
        }


        let is_last_layer = children.iter().all(|child| child.children().is_empty());

        let args: Vec<Expression> = if is_last_layer {
            children
                .iter()
                .map(|child| Expression::Literal(Literal::Atom(child.to_string())))
                .collect()
        } else {
            children
                .iter()
                .map(|child| {
                    let dyn_child = Dynamic::from_ast(child);
                    dynamic_to_expression(var_name, &dyn_child, is_primed, max_bit_map)
                })
                .collect()
        };

        return match decl_name.as_str() {
            "and" => Expression::MAnd(args.into_iter().map(Box::new).collect()),
            "or"  => Expression::MOr(args.into_iter().map(Box::new).collect()),
            "not" => {
                assert_eq!(args.len(), 1);
                Expression::Neg(Box::new(args[0].clone()))
            }
            "=" => {
                let children = node.children();
                if children.len() == 2 {
                    let left = &children[0];
                    let right = &children[1];
                    let left_str = left.to_string();
                    let right_str = right.to_string();


                    // Only continue if either side is an integer literal
                    if left_str.parse::<i64>().is_ok() || right_str.parse::<i64>().is_ok() {
                        // Case 1: var = constant
                        if let Ok(val) = right_str.parse::<i64>() {
                            let var_name = left.decl().name().to_string();
                            let mut cleaned_name = var_name
                                .find(|c: char| c == '!' || c == '_')
                                .map(|idx| var_name[..idx].to_string())
                                .unwrap_or_else(|| var_name.clone());

                            // TBD: is there "cleaner" variable names I can get?
                            if let Some(stripped) = cleaned_name.strip_suffix("_0_init") {
                                cleaned_name = stripped.to_string();
                            } else if let Some(stripped) = cleaned_name.strip_suffix("_0") {
                                cleaned_name = stripped.to_string();
                            } else if let Some(stripped) = cleaned_name.strip_suffix("_1") {
                                cleaned_name = format!("{}'", stripped);
                            }

                            // println!("Cleaned variable name: {}", cleaned_name);

                            if let Some(bitwidth) = max_bit_map.get(&cleaned_name) {
                                return build_bitblasted_equality(&cleaned_name, val, *bitwidth, is_primed);
                            } else {
                                panic!("No bitwidth found for variable '{}'", cleaned_name);
                            }
                        }

                        // Case 2: constant = var
                        if let Ok(val) = left_str.parse::<i64>() {
                            let var_name = right.decl().name().to_string();
                            let mut cleaned_name = var_name
                                .find(|c: char| c == '!' || c == '_')
                                .map(|idx| var_name[..idx].to_string())
                                .unwrap_or_else(|| var_name.clone());

                            // TBD: is there "cleaner" variable names I can get?
                            if let Some(stripped) = cleaned_name.strip_suffix("_0_init") {
                                cleaned_name = stripped.to_string();
                            } else if let Some(stripped) = cleaned_name.strip_suffix("_0") {
                                cleaned_name = stripped.to_string();
                            } else if let Some(stripped) = cleaned_name.strip_suffix("_1") {
                                cleaned_name = format!("{}'", stripped);
                            }

                            // println!("Cleaned variable name: {}", cleaned_name);

                            if let Some(bitwidth) = max_bit_map.get(&cleaned_name) {
                                return build_bitblasted_equality(&cleaned_name, val, *bitwidth, is_primed);
                            } else {
                                panic!("No bitwidth found for variable '{}'", cleaned_name);
                            }
                        }
                    } else {
                        let left = dynamic_to_expression(var_name, &Dynamic::from_ast(&children[0]), is_primed, max_bit_map);
                        let right = dynamic_to_expression(var_name, &Dynamic::from_ast(&children[1]), is_primed, max_bit_map);
                        return Expression::Iff(Box::new(left), Box::new(right));
                    }
                }

                // Fallback to Iff for Bool = Bool or unknown
                Expression::Iff(Box::new(args[0].clone()), Box::new(args[1].clone()))
            }
            "if"  => Expression::Implies(Box::new(args[0].clone()), Box::new(args[1].clone())),
            "ite" => {
                // Convert to (cond → then) ∧ (¬cond → else)
                Expression::And(
                    Box::new(Expression::Implies(Box::new(args[0].clone()), Box::new(args[1].clone()))),
                    Box::new(Expression::Implies(
                        Box::new(Expression::Neg(Box::new(args[0].clone()))),
                        Box::new(args[2].clone()),
                    )),
                )
            }
            _     => Expression::Literal(Literal::Atom(format!("UNKNOWN({})", decl_name))),
        };
    } else if sort_kind == SortKind::Int {
        let children = node.children();

        if children.is_empty() {

            let node_str = node.to_string();

            // Check if the node string is an integer constant
            if let Ok(parsed) = node_str.parse::<i64>() {
                let bitwidth = *max_bit_map.get(var_name).unwrap_or(&1);
                return build_bitblasted_equality(&var_name, parsed, bitwidth, is_primed);
            }          

            let mut cleaned_name = decl_name
                .find(|c: char| c == '!' || c == '_')
                .map(|idx| decl_name[..idx].to_string())
                .unwrap_or_else(|| decl_name.clone());
            if let Some(stripped) = cleaned_name.strip_suffix("_0_init") {
                cleaned_name = stripped.to_string();
            } else if let Some(stripped) = cleaned_name.strip_suffix("_0") {
                cleaned_name = stripped.to_string();
            } else if let Some(stripped) = cleaned_name.strip_suffix("_1") {
                cleaned_name = format!("{}'", stripped);
            }

            if is_primed {
                cleaned_name.push('\'');
            }

            return Expression::Literal(Literal::Atom(cleaned_name));
        }

        // Handle binary arithmetic ops: +, -, =, etc.
        // TODO: nested operation might fail
        let is_last_layer = children.iter().all(|child| child.children().is_empty());

        let args: Vec<Expression> = if is_last_layer {
            children
                .iter()
                .map(|child| Expression::Literal(Literal::Atom(child.to_string())))
                .collect()
        } else {
            children
                .iter()
                .map(|child| {
                    let dyn_child = Dynamic::from_ast(child);
                    dynamic_to_expression(var_name, &dyn_child, is_primed, max_bit_map)
                })
                .collect()
        };

        // TODO: here you need the bit-blasting, take care of all expressions in z3
        return match decl_name.as_str() {
           "+" | "-" | "*" | "/" | "mod" => {
                // Parse offset from args[1]
                let offset = match &args[1] {
                    Expression::Literal(Literal::Atom(s)) => {
                        s.parse::<i64>().unwrap_or_else(|_| {
                            eprintln!("Expected integer literal as offset, got '{}'", s);
                            std::process::exit(1);
                        })
                    }
                    Expression::Neg(inner) => {
                        if let Expression::Literal(Literal::Atom(s)) = &**inner {
                            s.parse::<i64>().map(|v| -v).unwrap_or_else(|_| {
                                eprintln!("Expected integer literal in negation, got '-{}'", s);
                                std::process::exit(1);
                            })
                        } else {
                            eprintln!("Unsupported negation expression format for offset.");
                            std::process::exit(1);
                        }
                    }
                    other => {
                        eprintln!("Unsupported expression format for offset: {:?}", other);
                        std::process::exit(1);
                    }
                };

                // Get bitwidth and upper bound
                let Some(bitwidth) = max_bit_map.get(var_name).copied() else {
                    panic!("Missing bitwidth for variable '{}'", var_name);
                };
                let bound = 1 << bitwidth;

                // Build transitions based on operator
                let transitions: Vec<Expression> = (0..bound as i64)
                    .filter_map(|val: i64| {
                        let result = match decl_name.as_str() {
                            "+" => val.checked_add(offset),
                            "-" => val.checked_sub(offset),
                            "*" => val.checked_mul(offset),
                            "/" => {
                                if offset == 0 {
                                    None
                                } else {
                                    Some(val / offset)
                                }
                            }
                            "mod" => {
                                if offset == 0 {
                                    None
                                } else {
                                    Some(val % offset)
                                }
                            }
                            _ => None,
                        };

                        match result {
                            Some(new_val) if new_val >= 0 && new_val < bound as i64 => {
                                let pre = build_bitblasted_equality(var_name, val, bitwidth, false);
                                let post = build_bitblasted_equality(var_name, new_val, bitwidth, true);
                                Some(Expression::Implies(Box::new(pre), Box::new(post)))
                            }
                            _ => None,
                        }
                    })
                    .collect();

                Expression::MAnd(transitions.into_iter().map(Box::new).collect())
            }
            // "-" => Expression::Sub(Box::new(args[0].clone()), Box::new(args[1].clone())),
                _   => Expression::Literal(Literal::Atom(format!("UNKNOWN_INT({})", decl_name))),
            };
    } 
    // If it's not a Bool, fall back
    Expression::Literal(Literal::Atom(format!("{:?}", node)))
}


// HELPER: bit-blast a variable with expression (var_name = val)
fn build_bitblasted_equality(var_name: &str, val: i64, bitwidth: usize, is_primed: bool) -> Expression {
    // Compute the minimum number of bits needed to represent `val` in two's complement
    let needed_bits = if val >= 0 {
        64 - val.leading_zeros()
    } else {
        64 - (!val).leading_zeros() + 1
    };

    if (needed_bits as usize) > bitwidth {
        eprintln!(
            "Error: bitwidth {} is too small to represent value {} for variable '{}'",
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
            Expression::Literal(Literal::Atom(bit_name))
        } else {
            Expression::Neg(Box::new(Expression::Literal(Literal::Atom(bit_name))))
        };
        bits.push(Box::new(bit_expr));
    }

    Expression::MAnd(bits)
}

pub fn get_expression(file: &str,debug: bool) -> String{
    let contents = fs::read_to_string(file)
        .expect("Should have been able to read the file");
    return contents;
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


// TODO: This will be replaced by Milad's code
// quantifiers: place to store quantifiers gotten from formula
// formula: the formula to parse
// complete_bit_map: hash map that stores (variable: max_bit_order) for bit-blasting
fn hq_parser(mut quantifiers: Vec<(String, String)>, formula: String, debug: bool, complete_bit_map: HashMap<String, i32>) -> (String, Vec<(String, String)>) {

    let quantifier_pattern = Regex::new(r"(Forall|Exists)\s+([A-Za-z_][A-Za-z0-9_]*)\.").unwrap();

    // let mut quantifiers: Vec<(String, String)> = Vec::new();
    let mut remaining_formula = formula.to_string();
    
    for cap in quantifier_pattern.captures_iter(&formula.clone()) {
        if let (Some(quantifier), Some(variable)) = (cap.get(1), cap.get(2)) {
            quantifiers.push((quantifier.as_str().to_string(), variable.as_str().to_string()));
        }
        remaining_formula = quantifier_pattern.replace(&remaining_formula, "").to_string();
    }
    let pattern = Regex::new(r"\[(.*?)\]").unwrap();

    // let modified_formula = pattern.replace_all(&remaining_formula, "_$1");

    if debug {
        println!("Quantifiers and Variables: {:?}", quantifiers); 
        // println!("Remaining Formula: {}", remaining_formula.trim());
        // println!("Modified Formula: {}", modified_formula);
    }

    let re = Regex::new(r#"\*\s*(\w+(?:\[\w+\])*)\[(\w+)\]\s*=\s*(\d+|\w+(?:\[\w+\])*\[(\w+)\])\s*\*"#).unwrap();
    if debug {
        // Function to process and print matches
        for captures in re.captures_iter(&remaining_formula.clone()) {
            // Extract matched groups
            let var1 = captures.get(1).map_or("", |m| m.as_str());
            let bracket1 = captures.get(2).map_or("", |m| m.as_str());
            let rhs = captures.get(3).map_or("", |m| m.as_str());

            // is rhs a variable or an integer
            if let Some(int_match) = captures.get(3).and_then(|m| m.as_str().parse::<i32>().ok()) {
                println!("Pattern: var = int");
                println!("var = {}", var1);
                println!("bracket = {}", bracket1);
                println!("value = {}", int_match);
            } else if let Some(var_match) = captures.get(3) {
                let var2 = var_match.as_str();
                let bracket2 = captures.get(4).map_or("", |m| m.as_str());
                println!("Pattern: var = var");
                println!("var1 = {}", var1);
                println!("bracket1 = {}", bracket1);
                let mut var3 : &str = "";
                if let Some(last_open_bracket_idx) = var2.rfind('[') {
                    // Remove the substring from the last '[' to the end
                    var3 = &var2[..last_open_bracket_idx]; }
                println!("var2 = {}", var3);
                println!("bracket2 = {}", bracket2);
            }
            println!();
        }
    }

    let mut replacements = Vec::new();

    let binding = remaining_formula.clone();
    // Function to process matches and store replacements
    for captures in re.captures_iter(&binding) {
        // Extract matched groups
        let var1 = captures.get(1).map_or("", |m| m.as_str());
        let bracket1 = captures.get(2).map_or("", |m| m.as_str());
        let rhs = captures.get(3).map_or("", |m| m.as_str());
        
        // pattern : var = int
        let new_pattern = if let Some(_) = rhs.parse::<i32>().ok() {
            let max_bit = *complete_bit_map.get(var1).unwrap_or(&0);
            if max_bit == 0 {
                panic!("Variable not found in bit map!");
            }
            // println!("MAX_BIT: {}", max_bit);
            manipulate_pattern(max_bit, var1, bracket1, rhs, None)
        // pattern : var = var
        } else {
            // println!("RHS: {}", rhs);
            let mut var2 : &str = "";
            if let Some(last_open_bracket_idx) = rhs.rfind('[') {
                // Remove the substring from the last '[' to the end
                var2 = &rhs[..last_open_bracket_idx];

            }
            // println!("RHS_change: {}", var2);
            // let var2 = rhs;
            let bracket2 = captures.get(4).map_or("", |m| m.as_str());
            // find max of each var's max_bit value
            let max_bit_1 = *complete_bit_map.get(var1).unwrap_or(&0);
            // println!("MAX_BIT_1: {}", max_bit_1);
            let max_bit_2 = *complete_bit_map.get(var2).unwrap_or(&0);
            // println!("MAX_BIT_2: {}", max_bit_2);

            if max_bit_1 == 0 || max_bit_2 == 0 {
                panic!("Variable not found in bit map!");
            }
            let max_bit = max_bit_1.max(max_bit_2);
            manipulate_pattern(max_bit, var1, bracket1, var2, Some(bracket2))
        };

        // Store the original match and the new pattern
        if let Some(matched) = captures.get(0) {
            replacements.push((matched.as_str(), new_pattern));
        }
    }

    // Replace all matches in the original string
    for (original, replacement) in replacements {
        if debug {
            println!("Original: {}, Replacement: {}", original, replacement);
        }
        remaining_formula = remaining_formula.replace(original, &replacement);
    }

    let pattern = Regex::new(r"\\d+|[a-zA-Z'_0-9\[\].]+").unwrap();
    let mut form = remaining_formula.clone();
    // for cap in pattern.captures_iter(&remaining_formula){
    //     // if cap has [] then it is a variable, so replace the last [thing] with _thing
    //     let matched = cap.get(0).unwrap();
    //     if matched.as_str().contains("[") { // its a variable
    //         let mut variable = matched.as_str().to_owned();
    //         variable = replace_last_occurrence(&variable, "]", "");
    //         variable = replace_last_occurrence(&variable, "[", "_");
    //         form = form.replace(matched.as_str(), &*variable);
    //     }}
    // if debug {
    //     println!("Quantifiers and Variables: {:?}", quantifiers);
    //     println!("Remaining Formula: {}", remaining_formula.trim());
    //     println!("Modified Formula: {}", form);
    //     raise_error("Completed HQ Parser",1);
    // }

    return (form, quantifiers);
}


