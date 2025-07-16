extern crate regex;

use std::collections::HashMap;
use z3::{Config, Context};
use z3::ast::{Bool, Int};
use z3::ast::Ast; // needed for `.eq()` etc.
use z3::ast::Dynamic;
use ir::{SMVEnv, VarType, Variable, ReturnType, EnvState};
use z3::Sort;

use std::fs::File;
use std::io::{self, Write};
use std::process::{Command, Stdio};
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::ops::Add;

use ir::int_var;
use ir::bool_var;

use std::ops::Sub;

#[derive(Debug)]
struct Transition {
    curr: HashMap<String, String>,
    next: HashMap<String, String>,
    cond: Option<String>,
}

struct Args {
    input_path: String,
    output_path: Option<String>,
    bit_encode: bool,
    input_format: String,
    output_format: String,
}


// For traditional primed format
pub fn parse_args() -> Args {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <input-file> [--bit-encode] [--input-format trans|model] [--output-format primed|functions] [--output <file>]", args[0]);
        std::process::exit(1);
    }

    let mut input_path = None;
    let mut output_path = None;
    let mut bit_encode = false;
    let mut input_format = "trans".to_string();
    let mut output_format = "primed".to_string();

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--bit-encode" => {
                bit_encode = true;
                i += 1;
            }
            "--output" => {
                if i + 1 >= args.len() {
                    eprintln!("Expected a filename after --output");
                    std::process::exit(1);
                }
                output_path = Some(args[i + 1].clone());
                i += 2;
            }
            "--input-format" => {
                if i + 1 >= args.len() {
                    eprintln!("Expected a format after --input-format");
                    std::process::exit(1);
                }
                input_format = args[i + 1].clone();
                i += 2;
            }
            "--output-format" => {
                if i + 1 >= args.len() {
                    eprintln!("Expected a format after --output-format");
                    std::process::exit(1);
                }
                output_format = args[i + 1].clone();
                i += 2;
            }
            arg if input_path.is_none() => {
                input_path = Some(arg.to_string());
                i += 1;
            }
            _ => {
                eprintln!("Unknown or duplicated argument: {}", args[i]);
                std::process::exit(1);
            }
        }
    }

    let input_path = input_path.expect("Missing input file");

    Args {
        input_path,
        output_path,
        bit_encode,
        input_format,
        output_format,
    }
}


pub fn parse_block(lines: &[String]) -> Transition {
    let assign_re = Regex::new(r"^(\w+)\s*=\s*(TRUE|FALSE|\d+)$").unwrap();
    let next_re = Regex::new(r"^next\((\w+)\)\s*=\s*(TRUE|FALSE|\d+)$").unwrap();
    let mut curr = HashMap::new();
    let mut next = HashMap::new();

    for line in lines {
        if let Some(cap) = assign_re.captures(line) {
            curr.insert(cap[1].to_string(), cap[2].to_string());
        } else if let Some(cap) = next_re.captures(line) {
            next.insert(cap[1].to_string(), cap[2].to_string());
        }
    }
    Transition { curr, next, cond: None }
}

pub fn parse_transitions(content: &str) -> Vec<Transition> {
    let trans_start_re = Regex::new(r"Trans:").unwrap();
    let mut transitions = vec![];
    let mut current_block = vec![];

    for line in content.lines().map(|l| l.trim().to_string()) {
        if trans_start_re.is_match(&line) {
            if !current_block.is_empty() {
                transitions.push(parse_block(&current_block));
                current_block.clear();
            }
        } else {
            current_block.push(line);
        }
    }
    if !current_block.is_empty() {
        transitions.push(parse_block(&current_block));
    }
    transitions
}

pub fn generate_format_primed(transitions: &[Transition], bit_encode: bool) -> String {
    let mut all_vars = BTreeSet::new();
    let mut formulas = vec![];

    for t in transitions {
        for k in t.curr.keys() {
            all_vars.insert(k.clone());
        }
        for k in t.next.keys() {
            all_vars.insert(k.clone());
        }
    }

    for t in transitions {
        let mut curr_expr = vec![];
        let mut next_expr = vec![];

        for var in all_vars.iter() {
            if let Some(val) = t.curr.get(var) {
                curr_expr.extend(to_literal(var, val, false, bit_encode));
            }
            if let Some(val) = t.next.get(var) {
                next_expr.extend(to_literal(var, val, true, bit_encode));
            }
        }

        formulas.push(format!("(({})->({}))", curr_expr.join("/\\"), next_expr.join("/\\")));
    }

    formulas.join("/\\\n")
}


// For SMT unrolling in python
pub fn to_literal(var: &str, val: &str, primed: bool, bit_encode: bool) -> Vec<String> {
    if bit_encode {
        if let Ok(n) = val.parse::<u32>() {
            let bit_width = {
                let mut width = 0;
                let mut temp = n;
                while temp > 0 {
                    temp >>= 1;
                    width += 1;
                }
                width.max(1)
            };

            return (0..bit_width)
                .rev()
                .map(|i| {
                    let bit = (n >> i) & 1;
                    let name = format!("{}_{}", var, bit_width - 1 - i);
                    let name = if primed { format!("{}'", name) } else { name };
                    if bit == 1 {
                        name
                    } else {
                        format!("~{}", name)
                    }
                })
                .collect();
        }
    }

    let name = if primed { format!("{}'", var) } else { var.to_string() };
    if val == "TRUE" {
        vec![name]
    } else if val == "FALSE" {
        vec![format!("~{}", name)]
    } else {
        vec![format!("{}={}", name, val)]
    }
}

pub fn parse_flattened_fsm(content: &str) -> Vec<Transition> {
    let mut transitions: Vec<Transition> = vec![];
    let mut curr_state: HashMap<String, String> = HashMap::new();
    let mut current_var: Option<String> = None;
    let mut in_case = false;
    for line in content.lines().map(str::trim) {
        if line.starts_with("init(") {
            if let Some(init_line) = line.strip_prefix("init(").and_then(|l| l.strip_suffix(";")) {
                if let Some((var, val)) = init_line.split_once(") := ") {
                    curr_state.insert(var.to_string(), val.to_string());
                }
            }
        } else if line.starts_with("next(") {
            current_var = line.strip_prefix("next(").and_then(|l| l.strip_suffix(") := case")).map(str::to_string);
            in_case = true;
        } else if in_case && line == "esac;" {
            in_case = false;
            current_var = None;
        } else if in_case {
            if let Some(var) = &current_var {
                if let Some((cond, val)) = line.strip_suffix(";").and_then(|l| l.split_once(":")) {
                    let mut next = HashMap::new();
                    next.insert(var.clone(), val.trim().to_string());
                    transitions.push(Transition {
                        curr: curr_state.clone(),
                        next,
                        cond: Some(cond.trim().to_string()),
                    });
                }
            }
        }
    }
    transitions
}

pub fn translate_condition(raw: &str) -> String {
    let trimmed = raw.trim();
    if trimmed.eq_ignore_ascii_case("TRUE") {
        return "True".to_string();
    }

    let expr = trimmed
        .replace("!", "not ")
        .replace("&", " and ")
        .replace("|", " or ")
        .replace("=", "==");

    let mut tokens: Vec<String> = vec![];
    for tok in expr.split_whitespace() {
        match tok {
            "and" | "or" | "not" | "(" | ")" | "==" | "!=" => tokens.push(tok.to_string()),
            val if val.parse::<i32>().is_ok() => tokens.push(val.to_string()),
            var => tokens.push(format!("c['{}']", var.trim_matches(&['(', ')'][..]))),
        }
    }

    let cond_str = tokens.join(" ");
    if cond_str.contains("and") && !cond_str.contains("or") {
        let parts: Vec<String> = cond_str
            .split("and")
            .map(|s| {
                let trimmed = s.trim();
                if trimmed.starts_with("not ") {
                    let inner = trimmed.trim_start_matches("not ").trim().to_string();
                    format!("Not({})", inner)
                } else {
                    trimmed.to_string()
                }
            })
            .collect();
        return format!("And({})", parts.join(", "));
    }
    cond_str
}

pub fn translate_action(val: &str) -> String {
    let val = val.trim();
    if val == "TRUE" {
        "True".to_string()
    } else if val == "FALSE" {
        "False".to_string()
    } else if val.contains("union") {
        let parts = val.split("union").map(|s| translate_action(s.trim())).collect::<Vec<_>>();
        format!("[{}]", parts.join(", "))
    } else if val.parse::<i32>().is_ok() {
        val.to_string()
    } else if val.contains("+") {
        val.split('+')
            .map(|t| {
                let tok = t.trim();
                if tok.parse::<i32>().is_ok() {
                    tok.to_string()
                } else {
                    format!("c['{}']", tok)
                }
            })
            .collect::<Vec<_>>()
            .join(" + ")
    } else {
        val.to_string()
    }
}

pub fn generate_format_functions(transitions: &[Transition]) -> String {
    let mut init_vals = BTreeMap::new();
    let mut ranges = BTreeMap::new();
    let mut trans_map: HashMap<String, Vec<(String, String)>> = HashMap::new();

    for t in transitions {
        for (var, val) in &t.curr {
            init_vals.entry(var.clone()).or_insert(val.clone());
            if let Ok(n) = val.parse::<i32>() {
                ranges.entry(var.clone()).or_insert((n, n));
                let r = ranges.get_mut(var).unwrap();
                r.0 = r.0.min(n);
                r.1 = r.1.max(n);
            }
        }

        for (var, val) in &t.next {
            let cond_expr = t.cond.as_ref().map_or("True".to_string(), |c| translate_condition(c));
            let act_expr = translate_action(val);
            trans_map.entry(var.clone()).or_default().push((format!("lambda c: {}", cond_expr), format!("lambda c: {}", act_expr)));
        }
    }

    let mut output = String::new();
    for (var, val) in &init_vals {
        if let Ok(_) = val.parse::<i32>() {
            let (min, max) = ranges[var];
            output += &format!("env.add_var('{}', ({}, {}), {})\n", var, min, max, val);
        } else {
            output += &format!("env.add_var('{}', 'bool', {})\n", var, val.to_lowercase());
        }
    }
    output += "\n";
    for (var, trans) in &trans_map {
        for (cond, act) in trans {
            output += &format!("env.add_transition('{}', {}, {})\n", var, cond, act);
        }
    }
    output
}




// ====================================================================================



/// Represents a parsed variable type from NuXMV
#[derive(Debug, Clone)]
pub enum ParsedVarType {
    Bool { init: Option<Vec<bool>> },
    Int  { init: Option<Vec<i64>>, lower: Option<i64>, upper: Option<i64> },
}

/// Represents a parsed variable, including name and type
#[derive(Debug, Clone)]
pub struct ParsedVariable {
    pub name: String,
    pub sort: ParsedVarType,
}

/// Holds all parsed information from a NuXMV flattened model
#[derive(Debug)]
pub struct ParsedModel {
    pub variables: Vec<ParsedVariable>,
    pub inits: HashMap<String, String>,
    pub transitions: Vec<(String, String, String)>,
    pub predicates: HashMap<String, String>,
}

// issue: losing
// pub fn parse_flattened_nuxmv(input: &str) -> ParsedModel {
//     let mut variables = Vec::new();
//     let mut inits = HashMap::new();
//     let mut transitions: Vec<(String, String, String)> = vec![];
//     let mut predicates = HashMap::new();


//     // Parse VAR section
//     let var_decl_re = Regex::new(r"(?m)^\s*(\w+)\s*:\s*([\w{},\s]+);").unwrap();
//     for cap in var_decl_re.captures_iter(input) {
//         let name = cap[1].to_string();
//         let typ_raw = cap[2].trim();

//         // patch: TRUE somehow get registered unintentionally
//         let reserved = ["TRUE", "FALSE"];
//         if reserved.contains(&name.as_str()) {
//             continue; // Skip reserved keywords
//         }

//         let sort = 
//         if typ_raw == "boolean" {
//             ParsedVarType::Bool { init: None }
//         } else if typ_raw.starts_with('{') && typ_raw.ends_with('}') {
//             // Parse enumerated set as bounded Int domain
//             let values: Vec<i64> = typ_raw[1..typ_raw.len() - 1]
//                 .split(',')
//                 .filter_map(|s| s.trim().parse::<i64>().ok())
//                 .collect();

//             if values.is_empty() {
//                 // Invalid set: treat as unbounded int --> should not happen 
//                 ParsedVarType::Int {
//                     init: None,
//                     lower: None,
//                     upper: None,
//                 }
//             } else {
//                 let (min, max) = values
//                     .iter()
//                     .fold((i64::MAX, i64::MIN), |(lo, hi), &v| (lo.min(v), hi.max(v)));

//                 ParsedVarType::Int {
//                     init: None,
//                     lower: Some(min),
//                     upper: Some(max),
//                 }
//             }
//         } else {
//             // fallback: treat unknown types as unbounded integer
//             ParsedVarType::Int {
//                 init: None,
//                 lower: None,
//                 upper: None,
//             }
//         };

//         variables.push(
//             ParsedVariable {
//                 name,
//                 sort,
//             },
//         );
//     }

//     // Parse ASSIGN init(...) := ...
//     let init_re = Regex::new(r"init\((\w+)\)\s*:=\s*(.+);").unwrap();
//     for cap in init_re.captures_iter(input) {
//         let var = cap[1].to_string();
//         let val = cap[2].trim().trim_end_matches(';').to_string();
//         inits.insert(var, val);
//     }

//     // Parse ASSIGN next(...) := ...
//     let next_assign_re = Regex::new(r"next\((\w+)\)\s*:=\s*(.*)").unwrap();
//     let mut lines = input.lines().map(str::trim).peekable();
//     let mut current_var: Option<String> = None;
//     while let Some(line) = lines.next() {
//         if let Some(cap) = next_assign_re.captures(line) {
//             let var = cap[1].to_string();
//             let rhs = cap[2].trim();

//             if rhs.starts_with("case") {
//                 // Start collecting the full case block
//                 let mut case_lines = Vec::new();

//                 // First line may include guard (e.g., "case x : y + 1;")
//                 if let Some(after_case) = rhs.strip_prefix("case").map(str::trim) {
//                     if !after_case.is_empty() {
//                         case_lines.push(after_case.to_string());
//                     }
//                 }

//                 while let Some(l) = lines.next() {
//                     let trimmed = l.trim();
//                     if trimmed.eq_ignore_ascii_case("esac;") {
//                         break;
//                     }
//                     case_lines.push(trimmed.to_string());
//                 }

//                 for case_line in case_lines {
//                     if let Some((guard, update)) = case_line.split_once(':') {
//                         let guard = guard.trim().to_string();
//                         let update = update.trim().trim_end_matches(';').to_string();
//                         transitions.push((var.clone(), guard, update));
//                     }
//                 }
//             } else {
//                 // It's a simple assignment: next(x) := expr;
//                 let update = rhs.trim_end_matches(';').to_string();
//                 transitions.push((var, "TRUE".to_string(), update));
//             }
//         }
//     }
//     // println!("{:#?}", transitions); // DEBUG

//     ParsedModel {
//         variables,
//         inits,
//         transitions,
//         predicates,
//     }
// }

pub fn parse_original_smv(input: &str) -> ParsedModel {
    // println!("{}", input);
    let mut variables = Vec::new();
    let mut inits = HashMap::new();
    let mut transitions: Vec<(String, String, String)> = vec![];
    let mut predicates = HashMap::new();

    // Parse VAR section
    let var_decl_re = Regex::new(r"(?m)^\s*([\w.\[\]]+)\s*:\s*([\w{}\s.,]+);").unwrap();


    let mut lines = input.lines().peekable();
    // let mut var_lines = Vec::new();
    let mut in_var_section = false;

    while let Some(line) = lines.next() {
        let trimmed = line.trim();

        // println!{"???{}", trimmed};

        if trimmed.starts_with("VAR") {
            in_var_section = true;
            continue;
        }

        if in_var_section {
            if trimmed.starts_with("ASSIGN") {
                break; // stop collecting once ASSIGN is reached
            }
            if let Some(cap) = var_decl_re.captures(trimmed) {
                let name = strip_comment(&cap[1]).trim().to_string();
                let typ_raw = strip_comment(&cap[2]).trim();

                // println!("Name: {}", name);
                // println!("Type raw: {}", typ_raw);
                
                // patch: TRUE somehow get registered unintentionally
                let reserved = ["TRUE", "FALSE"];
                if reserved.contains(&name.as_str()) {
                    continue; // Skip reserved keywords
                }

                let sort = if typ_raw.eq_ignore_ascii_case("boolean") {
                    ParsedVarType::Bool { init: None }
                } else if typ_raw.contains("..") {
                    // Handle range format like "0..3"
                    let parts: Vec<&str> = typ_raw.split("..").collect();
                    if parts.len() == 2 {
                        let lower = parts[0].trim().parse::<i64>().ok();
                        let upper = parts[1].trim().parse::<i64>().ok();
                        ParsedVarType::Int {
                            init: None,
                            lower,
                            upper,
                        }
                    } else {
                        // Malformed range, treat as unbounded int
                        ParsedVarType::Int {
                            init: None,
                            lower: None,
                            upper: None,
                        }
                    }
                } else {
                    // fallback: treat unknown types as unbounded integer
                    println!("WARNING: Unknown type '{}', defaulting to Int for '{}'", typ_raw, name);
                    ParsedVarType::Int {
                        init: None,
                        lower: None,
                        upper: None,
                    }
                };
                variables.push(
                    ParsedVariable {
                        name,
                        sort,
                    },
                );
            }
        }
    }






    // Parse ASSIGN init(...) := ...
    let init_re = Regex::new(r"init\(([\w\[\]]+)\)\s*:=\s*\{?(.+?)\}?;").unwrap();
    for cap in init_re.captures_iter(input) {
        let var = cap[1].to_string();
        let val = strip_comment(&cap[2]).trim_end_matches(';').to_string();
        inits.insert(var, val);
    }


    // Parse ASSIGN next(...) := ...
    let next_assign_re = Regex::new(r"next\(([\w\[\]]+)\)\s*:=\s*(.*)").unwrap();
    let mut lines = input.lines().map(str::trim).peekable();

    while let Some(line) = lines.next() {
        let line = line.trim();


        // Skip comment lines
        if line.starts_with("--") || line.starts_with("#") || line.is_empty() {
            continue;
        }

        if let Some(cap) = next_assign_re.captures(line) {
            let var = cap[1].to_string();
            let mut rhs = strip_comment(cap.get(2).map_or("", |m| m.as_str())).to_string();


            // If RHS is empty, gather more lines
            if rhs.is_empty() {
                while let Some(next_line) = lines.peek() {
                    let next_line = next_line.trim();
                    if next_line.is_empty() || next_line.starts_with("--") {
                        lines.next(); // Consume and skip
                        continue;
                    }

                    rhs = next_line.to_string();
                    lines.next(); // Consume the line we used
                    break;
                }
            }

            if rhs.starts_with("case") {

                let mut case_lines = Vec::new();

                if let Some(after_case) = rhs.strip_prefix("case").map(str::trim) {
                    if !after_case.is_empty() && !after_case.eq_ignore_ascii_case("esac") {
                        case_lines.push(strip_comment(after_case).to_string());

                    }
                }

                while let Some(l) = lines.next() {
                    let trimmed = l.trim();
                    if trimmed.starts_with("--") || trimmed.is_empty() {
                        continue;
                    }

                    if trimmed.eq_ignore_ascii_case("esac;") {
                        break;
                    }

                    case_lines.push(strip_comment(trimmed).to_string());

                }

                for case_line in case_lines {
                    // println!("CASE: {}", case_line);
                    if let Some((guard, update)) = case_line.split_once(':') {
                        let guard = strip_comment(guard).trim().to_string();
                        let update = strip_comment(update).trim_end_matches(';').to_string();
                        transitions.push((var.clone(), guard, update));
                    }
                }
            } else {
                let update = rhs.trim_end_matches(';').to_string();
                transitions.push((var, "TRUE".to_string(), update));
            }
        }
    }
    // println!("{:#?}", transitions); // DEBUG

    // Parse DEFINE block
    if let Some(define_start) = input.find("DEFINE") {
        // Find start of DEFINE
        let rest = &input[define_start + "DEFINE".len()..];
        let mut define_block = String::new();

        for line in rest.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with("--") {
                continue;
            }
            if trimmed.starts_with("VAR") || trimmed.starts_with("ASSIGN") || trimmed.starts_with("MODULE") {
                break;
            }
            define_block.push_str(line);
            // println!("?? {}", define_block);
            define_block.push('\n');
        }

        let define_re = Regex::new(r"(?m)^\s*([\w.\[\]]+)\s*:=\s*(.+?);").unwrap();
        for cap in define_re.captures_iter(&define_block) {
            let var = strip_comment(&cap[1]).to_string();
            let expr = strip_comment(&cap[2]).to_string();
            predicates.insert(var, expr);
        }
    }

    ParsedModel {
        variables,
        inits,
        transitions,
        predicates,
    }
}

fn strip_comment(s: &str) -> &str {
    s.split("--").next().unwrap_or("").trim()
}

pub fn generate_smv_env_from_parsed<'ctx>(
    ctx: &'ctx Context,
    parsed: ParsedModel,
) -> SMVEnv<'ctx> {

    let mut env = SMVEnv::new(ctx);
    let mut interned_names: Vec<String> = vec![];

    // 1. Register variables
    for var in &parsed.variables {
        let init_val = parsed.inits.get(&var.name);


        let vtype = match &var.sort {
            ParsedVarType::Bool { .. } => {
                // println!("DEBUG vars: {}", var.name);
                let init = match init_val {
                    Some(v) => {
                        let upper = v.to_ascii_uppercase();
                        match upper.as_str() {
                            "TRUE" => Some(vec![true]),
                            "FALSE" => Some(vec![false]),
                            _ => None,
                        }
                    }
                    None => None,
                };
                VarType::Bool { init }
            }

            ParsedVarType::Int { lower, upper, .. } => {
                let init = match init_val {
                    Some(val) => {
                        let final_val = val
                            .split("union")
                            .filter_map(|s| s.trim().parse::<i64>().ok())
                            .last();
                        final_val.map(|v| vec![v])
                    }
                    None => None,
                };

                VarType::Int {
                    init,
                    lower: *lower,
                    upper: *upper,
                }
            }
        };

        let name_ref: &'ctx str = Box::leak(var.name.clone().into_boxed_str());
        env.register_variable(name_ref, vtype);
    }
    // DEBUG
    // println!("Registered variables:");
    for (name, var) in env.get_variables() {
        // println!("  {} -> {:?}", name, var.sort);
    }


    // 1.2 Register predicates (might be used in transitions)
    // println!("Registered predicates:");
    for (name, expr_str) in parsed.predicates.clone() {
        let name_ref: &'ctx str = Box::leak(name.clone().into_boxed_str());
        interned_names.push(name.clone());

        // println!("  {} := {}", name, expr_str); // debug

        let expr = expr_str.clone();
        let var_name = name.clone();

        env.register_predicate(
            name_ref,
            move |env, ctx: &'ctx Context, state: &EnvState<'ctx>| {
                let cond_fn = parse_condition(env, &expr, &var_name, &ParsedVarType::Bool { init: None });
                let result = cond_fn(ctx, state);
                match result {
                    ReturnType::DynAst(d) => d
                        .as_bool()
                        .unwrap_or_else(|| panic!("Predicate '{}' did not return Bool", var_name)),
                    _ => panic!("Expected DynAst for predicate '{}'", var_name),
                }
            },
        );
    }



    // 2. Register transitions
    // println!("Registered transitions:");
    for (name, guard, update) in parsed.transitions.clone() {
        let name_ref: &'ctx str = Box::leak(name.clone().into_boxed_str());
        interned_names.push(name.clone());

        // println!("  {} : {} -> {}", name, guard, update); // debug
        env.register_transition(
            name_ref,
            {
                let guard = guard.clone(); // capture in closure
                let var_name = name.clone();
                let parsed_var = parsed.variables.iter().find(|v| v.name == *name).unwrap();
                let var_type = parsed_var.sort.clone();
                move |env, ctx: &'ctx Context, state: &EnvState<'ctx>| {
                    parse_condition(env, &guard, &var_name, &var_type)(ctx, state)
                }
            },
            {
                let update = update.clone();
                let var_name = name.clone();
                let parsed_var = parsed.variables.iter().find(|v| v.name == *name).unwrap();
                let var_type = parsed_var.sort.clone();

                move |env, ctx: &'ctx Context, state: &EnvState<'ctx>| {
                    parse_action(env, &update, &var_name, &var_type)(ctx, state)
                }
            },
        );
    }

    env
}

pub fn parse_condition<'ctx>(
    smv_env: &SMVEnv<'ctx>,
    cond_str: &str,
    _var_name: &str,
    var_type: &ParsedVarType,
) -> impl Fn(&'ctx Context, &EnvState<'ctx>) -> ReturnType<'ctx> + 'static {
    // println!("DEBUG cond: {}: ", cond_str);
    let raw = cond_str.trim().to_owned();
    let vtype = var_type.clone(); // clone so we can move it into closure

    fn strip_outer_parens(s: &str) -> &str {
        let s = s.trim();
        if s.starts_with('(') && s.ends_with(')') {
            let mut depth = 0;
            for (i, c) in s.chars().enumerate() {
                match c {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 && i != s.len() - 1 {
                            return s; // Not just outermost parens
                        }
                    }
                    _ => {}
                }
            }
            return &s[1..s.len() - 1];
        }
        s
    }

    fn recurse<'ctx>(
    s: &str,
    ctx: &'ctx Context,
    state: &EnvState<'ctx>,
    ) -> Dynamic<'ctx> {
        let s = strip_outer_parens(s.trim());


        // Unary negation
        if let Some(inner) = s.strip_prefix('!') {
            let inner_expr = recurse(inner.trim(), ctx, state);
            let b = inner_expr.as_bool().unwrap_or_else(|| {
                panic!("Expected boolean after '!': {}", inner);
            });
            return b.not().into();
        }


        if s == "TRUE" {
            return Bool::from_bool(ctx, true).into();
        } else if s == "FALSE" {
            return Bool::from_bool(ctx, false).into();
        } else if let Ok(n) = s.parse::<i64>() {
            return Int::from_i64(ctx, n).into();
        }

        // Operators by precedence: lowest first
        let precedence = vec!['=', '&', '|', '+', '-'];

        for &op in &precedence {
            let mut depth = 0;
            let mut split_idx = None;

            // Right-to-left scan for left-associative split
            for (i, c) in s.char_indices().rev() {
                match c {
                    ')' => depth += 1,
                    '(' => depth -= 1,
                    _ if depth == 0 && c == op => {
                        split_idx = Some(i);
                        break;
                    }
                    _ => {}
                }
            }

            if let Some(i) = split_idx {
                let lhs = s[..i].trim();
                let rhs = s[i + 1..].trim();

                let lhs_expr = recurse(lhs, ctx, state);
                let rhs_expr = recurse(rhs, ctx, state);

                return match op {
                    '+' => lhs_expr.as_int().unwrap().add(&rhs_expr.as_int().unwrap()).into(),
                    '-' => lhs_expr.as_int().unwrap().sub(&rhs_expr.as_int().unwrap()).into(),
                    '=' => lhs_expr._eq(&rhs_expr).into(),
                    '&' => {
                        let l = lhs_expr.as_bool().unwrap_or_else(|| {
                            panic!("Expected bool lhs in '&': {}", lhs);
                        });
                        let r = rhs_expr.as_bool().unwrap_or_else(|| {
                            panic!("Expected bool rhs in '&': {}", rhs);
                        });
                        Bool::and(ctx, &[&l, &r]).into()
                    }
                    '|' => {
                        let l = lhs_expr.as_bool().unwrap_or_else(|| {
                            panic!("Expected bool lhs in '|': {}", lhs);
                        });
                        let r = rhs_expr.as_bool().unwrap_or_else(|| {
                            panic!("Expected bool rhs in '|': {}", rhs);
                        });
                        Bool::or(ctx, &[&l, &r]).into()
                    }
                    _ => unreachable!(),
                };
            }
        }

        // Variable access
        if let Some(dyn_var) = state.get(s) {
            dyn_var.clone()
        } else {
            panic!("Identifier '{}' not found in state!", s);
        }
    }

    move |ctx, state| {
        let expr = recurse(&raw, ctx, state);
        ReturnType::DynAst(expr)
    }
}


pub fn parse_action<'ctx>(
    env: &SMVEnv<'ctx>,
    cond_str: &str,
    _var_name: &str,
    var_type: &ParsedVarType,
) -> impl Fn(&'ctx Context, &EnvState<'ctx>) -> ReturnType<'ctx> + 'static {
    // println!("DEBUG action: {}: ", cond_str);
    let raw = cond_str.trim().to_owned();
    let vtype = var_type.clone(); // clone so we can move it into closure

    fn strip_outer_parens(s: &str) -> &str {
        let s = s.trim();
        if s.starts_with('(') && s.ends_with(')') {
            let mut depth = 0;
            for (i, c) in s.chars().enumerate() {
                match c {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 && i != s.len() - 1 {
                            return s; // Not just outermost parens
                        }
                    }
                    _ => {}
                }
            }
            return &s[1..s.len() - 1];
        }
        s
    }

    fn recurse<'ctx>(
    s: &str,
    ctx: &'ctx Context,
    state: &EnvState<'ctx>,
    ) -> Dynamic<'ctx> {
        let s = strip_outer_parens(s.trim());

        if s == "TRUE" {
            return Bool::from_bool(ctx, true).into();
        } else if s == "FALSE" {
            return Bool::from_bool(ctx, false).into();
        } else if let Ok(n) = s.parse::<i64>() {
            return Int::from_i64(ctx, n).into();
        }

        // Operators by precedence: lowest first
        let precedence = vec!['=', '&', '|', '+', '-'];

        for &op in &precedence {
            let mut depth = 0;
            let mut split_idx = None;

            // Right-to-left scan for left-associative split
            for (i, c) in s.char_indices().rev() {
                match c {
                    ')' => depth += 1,
                    '(' => depth -= 1,
                    _ if depth == 0 && c == op => {
                        split_idx = Some(i);
                        break;
                    }
                    _ => {}
                }
            }

            if let Some(i) = split_idx {
                let lhs = s[..i].trim();
                let rhs = s[i + 1..].trim();

                let lhs_expr = recurse(lhs, ctx, state);
                let rhs_expr = recurse(rhs, ctx, state);

                return match op {
                    '+' => lhs_expr.as_int().unwrap().add(&rhs_expr.as_int().unwrap()).into(),
                    '-' => lhs_expr.as_int().unwrap().sub(&rhs_expr.as_int().unwrap()).into(),
                    '=' => lhs_expr._eq(&rhs_expr).into(),
                    '&' => {
                        let l = lhs_expr.as_bool().unwrap_or_else(|| {
                            panic!("Expected bool lhs in '&': {}", lhs);
                        });
                        let r = rhs_expr.as_bool().unwrap_or_else(|| {
                            panic!("Expected bool rhs in '&': {}", rhs);
                        });
                        Bool::and(ctx, &[&l, &r]).into()
                    }
                    '|' => {
                        let l = lhs_expr.as_bool().unwrap_or_else(|| {
                            panic!("Expected bool lhs in '|': {}", lhs);
                        });
                        let r = rhs_expr.as_bool().unwrap_or_else(|| {
                            panic!("Expected bool rhs in '|': {}", rhs);
                        });
                        Bool::or(ctx, &[&l, &r]).into()
                    }
                    _ => unreachable!(),
                };
            }
        }

        // Variable access
        if let Some(dyn_var) = state.get(s) {
            dyn_var.clone()
        } else {
            panic!("Variable '{}' not found!", s);
        }
    }

    move |ctx, state| {
        let expr = recurse(&raw, ctx, state);
        ReturnType::DynAst(expr)
    }
}



fn write_commands_file(filename: &str, commands: &[String]) -> io::Result<()> {
    let mut file = File::create(filename)?;
    for cmd in commands {
        writeln!(file, "{}", cmd)?;
    }
    Ok(())
}

/// execute NuXMV to obtain the flatten model
fn run_nuxmv(commands_file: &str) -> io::Result<String> {
    println!("running nuXmv");
    // Command::new("/full/path/to/nuxmv")
    let output = Command::new("/Users/milad/Desktop/rust_tutorial/HyperRUSTY/nuXmv")
        .arg("-source")
        .arg(commands_file)
        .stdout(Stdio::piped())
        .spawn()?
        .wait_with_output()?;

    if output.status.success() {
        //DEBUG
        // let result = String::from_utf8_lossy(&output.stdout).to_string();
        // Ok(result)
        Ok("success".to_string())
    } else {
        let error = String::from_utf8_lossy(&output.stderr).to_string();
        Err(io::Error::new(io::ErrorKind::Other, error))
    }
}

/// Reads and parses the input file according to the given arguments, returning the output as a SMVEnv<'ctx>.
pub fn parse_smv<'ctx>(
    ctx: &'ctx Context,
    input_path: &str,
    output_path: Option<String>,
    bit_encode: bool,
    input_format: &str,
    output_format: &str,
) -> SMVEnv<'ctx>  {
    
    println!("Parsing: {}\n", input_path);

    let commands = vec![
        format!("read_model -i {}", input_path),
        "flatten_hierarchy".to_string(),
        "build_flat_model".to_string(),
        "write_flat_model -o flattened.txt".to_string(),
        "quit".to_string(),
    ];    

    let filename = "commands.txt";

    if let Err(e) = write_commands_file(filename, &commands) {
        eprintln!("Error writing commands file: {}", e);
    }

    // match run_nuxmv(filename) {
    //     Ok(_output) => println!("NuXMV checks passed, model parsed."),
    //     Err(e) => eprintln!("Error running NuXMV: {}", e),
    // }
    
    // How about not using NuXmv at all?
    // let content = std::fs::read_to_string("flattened.txt").expect("Failed to read input file");
    let content = std::fs::read_to_string(input_path).expect("Failed to read input file");

    // parse into desired format
    let transitions = match input_format {
        "trans" => parse_transitions(&content),
        "model" => parse_flattened_fsm(&content),
        other => panic!("Unknown input format: {}", other),
    };

    match output_format {
        "primed" => {
            let output = generate_format_primed(&transitions, bit_encode);
            if let Some(out_path) = output_path {
                std::fs::write(&out_path, &output).expect("Failed to write output file");
            } else {
                println!("{}", output);
            }
            panic!("Expected output format 'ir' to return SMVEnv, but got 'primed'");
        }
        "functions" => {
            let output = generate_format_functions(&transitions);
            if let Some(out_path) = output_path {
                std::fs::write(&out_path, &output).expect("Failed to write output file");
            } else {
                println!("{}", output);
            }
            panic!("Expected output format 'ir' to return SMVEnv, but got 'functions'");
        }
        "ir" => {
            let cfg = z3::Config::new();
            // let ctx = Box::leak(Box::new(z3::Context::new(&cfg)));
            // let parsed_model = parse_flattened_nuxmv(&content);
            let parsed_model = parse_original_smv(&content);
            generate_smv_env_from_parsed(ctx, parsed_model)
        }
        other => panic!("Unknown output format: {}", other),
    }
}
