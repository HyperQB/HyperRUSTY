extern crate regex;

// use parser_nusmv::flattener::flatten_nusmv;

use std::collections::HashMap;
use std::ops::Mul;
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
use std::iter::Peekable;
use std::str::Chars;
use std::str::FromStr;

use ir::int_var;
use ir::bool_var;
use ir::bv_var;
use ir::to_dyn;
use ir::choice_from_vec;
use ir::choice;
use ir::choice_int_to_dyn;
use expressions::{Expression, Literal as Lit, Quant};

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


pub fn parse_original_smv(input: &str) -> ParsedModel {
    // println!("{}", input);
    let mut variables = Vec::new();
    let mut inits = HashMap::new();
    let mut transitions: Vec<(String, String, String)> = vec![];
    let mut predicates = HashMap::new();

    // let input = &flatten_nusmv(input);


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
    let init_re = Regex::new(r"init\(([\w.\[\]]+)\)\s*:=\s*\{?(.+?)\}?;").unwrap();
    for cap in init_re.captures_iter(input) {
        let var = cap[1].to_string();
        let val = strip_comment(&cap[2]).trim_end_matches(';').to_string();
        inits.insert(var, val);
    }


    // Parse ASSIGN next(...) := ...
    let next_assign_re = Regex::new(r"next\(([\w.\[\]\.]+)\)\s*:=\s*(.*)").unwrap();
    let mut lines = input.lines().map(str::trim).peekable();

    while let Some(line) = lines.next() {
        let line = line.trim();

        // Skip comments or empty lines
        if line.starts_with("--") || line.starts_with("#") || line.is_empty() {
            continue;
        }

        if let Some(cap) = next_assign_re.captures(line) {
            let var = cap[1].to_string();
            let mut rhs = strip_comment(cap.get(2).map_or("", |m| m.as_str())).to_string();

            // Collect full RHS (possibly multiline), up to 'esac;' or terminating semicolon
            while !rhs.trim_end().ends_with(';') && !rhs.trim_end().eq_ignore_ascii_case("esac;") {
                if let Some(next_line) = lines.next() {
                    let next_line_trimmed = strip_comment(next_line.trim());
                    if next_line_trimmed.is_empty() || next_line_trimmed.starts_with("--") {
                        continue;
                    }
                    rhs.push(' ');
                    rhs.push_str(&next_line_trimmed);
                } else {
                    break;
                }
            }

            // === CASE statement ===
            if rhs.trim_start().starts_with("case") {
                let mut case_body = String::new();

                // Push what comes after `case` in the same line, if any
                if let Some(after_case) = rhs.trim_start().strip_prefix("case").map(str::trim) {
                    if !after_case.is_empty() && !after_case.eq_ignore_ascii_case("esac;") {
                        case_body.push_str(after_case);
                    }
                }

                // Accumulate lines until "esac;" is seen
                while !case_body.trim_end().ends_with("esac;") {
                    if let Some(next_line) = lines.next() {
                        let trimmed = strip_comment(next_line.trim());
                        if trimmed.is_empty() || trimmed.starts_with("--") {
                            continue;
                        }
                        case_body.push(' ');
                        case_body.push_str(&trimmed);
                    } else {
                        break;
                    }
                }

                // Remove final `esac;`
                case_body = case_body.trim().strip_suffix("esac;").unwrap_or(&case_body).to_string();

                // Split by semicolons to process each `guard : update;` block
                for entry in case_body.split(';') {
                    if let Some((guard, update)) = entry.split_once(':') {
                        transitions.push((
                            var.clone(),
                            strip_comment(guard).trim().to_string(),
                            strip_comment(update).trim().to_string(),
                        ));
                    }
                }
            } else {
                // === Normal (non-case) update ===
                let update = rhs.trim_end_matches(';').trim().to_string();
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

        let define_re = Regex::new(r"(?m)^\s*([\w.\[\]\.]+)\s*:=\s*(.+?);").unwrap();
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

impl From<ParsedVarType> for VarType {
    fn from(p: ParsedVarType) -> Self {
        match p {
            ParsedVarType::Bool { init } => VarType::Bool { init },
            ParsedVarType::Int { init, lower, upper } => VarType::Int {
                init,
                lower,
                upper,
            },
        }
    }
}

// Generate SMVEnv from the ParsedModel
pub fn generate_smv_env_from_parsed<'ctx>(
    ctx: &'ctx Context,
    parsed: ParsedModel,
) -> SMVEnv<'ctx> {

    let mut env = SMVEnv::new(ctx);

    // Step 1. Register variables
    for var in &parsed.variables {
        let init_val = parsed.inits.get(&var.name);
        // println!("init value: {:?}", init_val);
        let vtype = match &var.sort {
            ParsedVarType::Bool { .. } => {
                let init = match init_val {
                    Some(v) => {
                        let upper = v.to_ascii_uppercase();
                        match upper.as_str() {
                            "TRUE" => Some(vec![true]),
                            "FALSE" => Some(vec![false]),
                            _ => Some(vec![true,false]), // otherwise, it's non-det choices
                        }
                    }
                    None => None,
                };
                VarType::Bool { init }
            }

            ParsedVarType::Int { lower, upper, .. } => {
                let init = match init_val {
                    Some(val) => {
                        // collect all explicit choices, e.g., "0,1,2,3"
                        let parsed_vals: Vec<i64> = val
                            .split(',')
                            .filter_map(|s| s.trim().parse::<i64>().ok())
                            .collect();

                        if !parsed_vals.is_empty() {
                            Some(parsed_vals)
                        } else {
                            // if no explicit list parsed, try full domain if bounds are known
                            match (*lower, *upper) {
                                (Some(lo), Some(hi)) => {
                                    let (a, b) = if lo <= hi { (lo, hi) } else { (hi, lo) };
                                    Some((a..=b).collect::<Vec<i64>>())
                                }
                                _ => None, // bounds unknown; leave as None
                            }
                        }
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


    // Step 2: Register predicates
    for (name, expr) in parsed.predicates.clone() {
        let name_ref: &'ctx str = Box::leak(name.clone().into_boxed_str());
        let expr_owned = expr.clone();
        let var_name = Box::leak(name.clone().into_boxed_str());
        let var_type = Box::leak(Box::new(ParsedVarType::Bool { init: None }));
        // Build closure with access to SMVEnv and expression
        env.register_predicate(
            name_ref,
            {
                let expr_str = expr_owned.to_owned();
                let type_copy = var_type.clone();
                let name_copy = var_name.to_string();
                let dyn_fn = build_dyn_node(&env, &expr_str, &name_copy, &type_copy);

                move |_env, ctx, state| {
                    dyn_fn(_env, ctx, state)
                        .as_bool()
                        .unwrap_or_else(|| panic!("Predicate '{}' must return Bool", name_copy))
                }
            },
        );
    }

    // for (name, _) in &env.predicates { println!("Predicate: {}", name); }

    // Step 3: Register transitions
    for (name, guard, update) in &parsed.transitions {
        let name_ref: &'ctx str = Box::leak(name.clone().into_boxed_str());
        let guard_str = guard.clone();
        let update_str = update.clone();

        // println!("from {:?} to {:?}", guard_str, update_str);

        let var = parsed.variables.iter().find(|v| v.name == *name).unwrap_or_else(|| {
            panic!("Transition for undeclared variable '{}'", name);
        });
        let var_type = var.sort.clone();
        let name_guard = name.clone();
        let name_update = name.clone();

        let guard_fn = build_dyn_node(&env, &guard_str, &name_guard, &var_type);
        let update_fn = build_dyn_node(&env, &update_str, &name_update, &var_type);

        if update_str.trim_start().starts_with('{') && update_str.trim_end().ends_with('}') {
            let inner = update_str.trim().trim_start_matches('{').trim_end_matches('}').trim();

            // Non-deterministic sets with commas stay as before:
            if inner.contains(',') {
                let nondet_choice = match var_type {
                    ParsedVarType::Int { .. } => {
                        let vals: Vec<i64> = parse_braced_values(&update_str);
                        choice_from_vec!(Int, vals)
                    }
                    ParsedVarType::Bool { .. } => {
                        let vals: Vec<bool> = parse_bool_braced_values(&update_str);
                        choice_from_vec!(Bool, vals)
                    }
                };
                env.register_transition(
                    name_ref,
                    move |env_, ctx_, state_| ReturnType::DynAst(guard_fn(env_, ctx_, state_)),
                    move |_env, _ctx, _state| nondet_choice.clone(),
                );
            } else {
                // Single element inside braces: {TRUE}/{FALSE}/{42}/{var_name}
                if let Ok(n) = inner.parse::<i64>() {
                    let upd = mk_update_single_int(n);
                    env.register_transition(
                        name_ref,
                        move |env_, ctx_, state_| ReturnType::DynAst(guard_fn(env_, ctx_, state_)),
                        upd,
                    );
                } else {
                    let upper = inner.to_ascii_uppercase();
                    if upper == "TRUE" || upper == "FALSE" {
                        let upd = mk_update_single_bool(upper);
                        env.register_transition(
                            name_ref,
                            move |env_, ctx_, state_| ReturnType::DynAst(guard_fn(env_, ctx_, state_)),
                            upd,
                        );
                    } else {
                        // treat as {var_name}
                        let update_fn = build_dyn_node(&env, &inner, &name_update, &var_type);
                        env.register_transition(
                            name_ref,
                            move |_env, _ctx, state| ReturnType::DynAst(guard_fn(_env, _ctx, state)),
                            move |_env, _ctx, state| ReturnType::DynAst(update_fn(_env, _ctx, state)),
                        );
                        // let upd = mk_update_single_var(inner.to_string(), var_type.clone());
                        // env.register_transition(
                        //     name_ref,
                        //     move |env_, ctx_, state_| ReturnType::DynAst(guard_fn(env_, ctx_, state_)),
                        //     upd,
                        // );
                    }
                }
            }
        } else {
            env.register_transition(
                name_ref,
                move |_env, _ctx, state| ReturnType::DynAst(guard_fn(_env, _ctx, state)),
                move |_env, _ctx, state| ReturnType::DynAst(update_fn(_env, _ctx, state)),
            );
        }   
    }
    
    
    env
}


// Make a Bool literal updater: {TRUE} or {FALSE}
fn mk_update_single_bool(upper: String)
-> impl for<'ctx> Fn(&SMVEnv<'ctx>, &'ctx z3::Context, &EnvState<'ctx>) -> ReturnType<'ctx> + Clone
{
    // Capture by value
    let is_true = upper.eq_ignore_ascii_case("TRUE");
    move |_env, ctx, _state| {
        let b = z3::ast::Bool::from_bool(ctx, is_true);
        ReturnType::DynAst(b.into())
    }
}

// Make an Int literal updater: {42}
fn mk_update_single_int(n: i64)
-> impl for<'ctx> Fn(&SMVEnv<'ctx>, &'ctx z3::Context, &EnvState<'ctx>) -> ReturnType<'ctx> + Clone
{
    move |_env, ctx, _state| {
        let i = z3::ast::Int::from_i64(ctx, n);
        ReturnType::DynAst(i.into())
    }
}

// Make a “just use that variable” updater: {var_name}
fn mk_update_single_var(var_sym: String, var_type: ParsedVarType)
-> impl for<'ctx> Fn(&SMVEnv<'ctx>, &'ctx z3::Context, &EnvState<'ctx>) -> ReturnType<'ctx> + Clone
{
    move |_env, _ctx, state| {
        let name: &str = var_sym.as_str(); // pass &str to your macros
        let dyn_ast = match var_type {
            ParsedVarType::Int { .. }  => to_dyn!(int_var!(state, name)),
            ParsedVarType::Bool { .. } => to_dyn!(bool_var!(state, name)),
            // ParsedVarType::BVector { .. } => to_dyn!(bv_var!(state, name)),
        };
        ReturnType::DynAst(dyn_ast)
    }
}

pub fn parse_braced_values(raw: &str) -> Vec<i64> {
    raw.trim_matches(|c| c == '{' || c == '}')
        .split(',')
        .map(|s| {
            s.trim().parse::<i64>().unwrap_or_else(|_| {
                panic!(
                    "\n[Error in NuSMV] Invalid integer in brace list: '{}'\n",
                    s.trim()
                )
            })
        })
        .collect()
}

pub fn parse_bool_braced_values(raw: &str) -> Vec<bool> {
    raw.trim_matches(|c| c == '{' || c == '}')
        .split(',')
        .map(|s| match s.trim() {
            "TRUE" => true,
            "FALSE" => false,
            _ => panic!("Invalid boolean: {}", s),
        })
        .collect()
}


fn preprocess_nondet_expr(var: &str, s: &str) -> String {
    let set_expr_re = regex::Regex::new(r"\{([^}]+)\}").unwrap();
    set_expr_re.replace_all(s, |caps: &regex::Captures| {
        let disjuncts = caps[1]
            .split(',')
            .map(str::trim)
            .map(|val| format!("({} = {})", var, val))
            .collect::<Vec<_>>();
        format!("({})", disjuncts.join(" | "))
    }).to_string()
}


#[derive(Debug, Clone)]
enum Choice {
    Bool(Vec<bool>),
    Int(Vec<i64>),
    None,
}

// Return a dynamic node, given the condition (guard or update) string 
pub fn build_dyn_node<'ctx>(
    smv_env: &SMVEnv<'ctx>,
    cond_str: &str,
    var_name: &str,
    var_type: &ParsedVarType,
) -> impl Fn(&SMVEnv<'ctx>, &'ctx Context, &EnvState<'ctx>) -> Dynamic<'ctx> + 'static {

    // println!("NOW parsing: {:?}", cond_str);

    let raw = preprocess_nondet_expr(var_name, cond_str.trim()); // preprocess once
    let var_name = var_name.to_owned();

    move |smv_env: &SMVEnv<'ctx>, ctx: &'ctx Context, state: &EnvState<'ctx>| {
       fn recurse<'ctx>(
            smv_env: &SMVEnv<'ctx>,
            var_name: &str,
            s: &str,
            ctx: &'ctx Context,
            state: &EnvState<'ctx>,
        ) -> Dynamic<'ctx> {
            let s = s.trim();

            // Strip outermost parentheses if they enclose the full expression
            fn strip_parens(expr: &str) -> &str {
                let mut start = 0;
                let mut end = expr.len();
                let bytes = expr.as_bytes();
                while start < end && bytes[start] == b'(' && bytes[end - 1] == b')' {
                    let mut depth = 0;
                    let mut matched = true;
                    for (i, c) in expr[start..end - 1].chars().enumerate() {
                        match c {
                            '(' => depth += 1,
                            ')' => {
                                depth -= 1;
                                if depth == 0 && i < (end - start - 2) {
                                    matched = false;
                                    break;
                                }
                            }
                            _ => {}
                        }
                    }
                    if matched && depth == 1 {
                        start += 1;
                        end -= 1;
                    } else {
                        break;
                    }
                }
                &expr[start..end]
            }

            let s = strip_parens(s).trim();


            if let Some(inner) = s.strip_prefix('!') {
                let inner_expr = recurse(smv_env, var_name, inner.trim(), ctx, state);
                return inner_expr.as_bool().unwrap().not().into();
            }

            if s == "TRUE" {
                return Bool::from_bool(ctx, true).into();
            } else if s == "FALSE" {
                return Bool::from_bool(ctx, false).into();
            } else if let Ok(n) = s.parse::<i64>() {
                return Int::from_i64(ctx, n).into();
            }

            // trick: adding spaces for " mod " so it doesn't get confused with var name like "modifying"
            let precedence = vec!["|", "&", "!=", ">=", "<=", "=", ">", "<",  "*", " mod ", "/", "+", "-"];

            for op in &precedence {
                let mut depth = 0;
                let mut idx = None;

                let chars: Vec<char> = s.chars().collect();
                let mut i = 0;
                while i + op.len() <= s.len() {
                    match chars[i] {
                        '(' => {
                            depth += 1;
                            i += 1;
                            continue;
                        }
                        ')' => {
                            depth -= 1;
                            i += 1;
                            continue;
                        }
                        _ => {}
                    }
                    // Check for operator match at top-level
                    if depth == 0 && &s[i..i + op.len()] == *op {
                        idx = Some(i);
                        break;
                    }
                    i += 1;
                }

                if let Some(i) = idx {
                    let lhs = s[..i].trim();
                    let rhs = s[i + op.len()..].trim();
                    let lhs_expr = recurse(smv_env, var_name, lhs, ctx, state);
                    let rhs_expr = recurse(smv_env, var_name, rhs, ctx, state);

                    return match *op {
                        "+" => lhs_expr.as_int().unwrap().add(&rhs_expr.as_int().unwrap()).into(),
                        "-" => lhs_expr.as_int().unwrap().sub(&rhs_expr.as_int().unwrap()).into(),
                        "*" => lhs_expr.as_int().unwrap().mul(&rhs_expr.as_int().unwrap()).into(),
                        "/" => lhs_expr.as_int().unwrap().div(&rhs_expr.as_int().unwrap()).into(),
                        " mod " => lhs_expr.as_int().unwrap().modulo(&rhs_expr.as_int().unwrap()).into(),
                        "!=" => lhs_expr._eq(&rhs_expr).not().into(),
                        "=" => lhs_expr._eq(&rhs_expr).into(),
                        ">" => lhs_expr.as_int().unwrap().gt(&rhs_expr.as_int().unwrap()).into(),
                        "<" => lhs_expr.as_int().unwrap().lt(&rhs_expr.as_int().unwrap()).into(),
                        ">=" => lhs_expr.as_int().unwrap().ge(&rhs_expr.as_int().unwrap()).into(),
                        "<=" => lhs_expr.as_int().unwrap().le(&rhs_expr.as_int().unwrap()).into(),
                        "&" => {
                            let l = lhs_expr.as_bool().unwrap();
                            let r = rhs_expr.as_bool().unwrap();
                            Bool::and(ctx, &[&l, &r]).into()
                        }
                        "|" => {
                            let l = lhs_expr.as_bool().unwrap();
                            let r = rhs_expr.as_bool().unwrap();
                            Bool::or(ctx, &[&l, &r]).into()
                        }
                        other => {
                            panic!(
                                "illegal operator '{other}' in expression '{lhs_expr}' and '{rhs_expr}'! please check the NuSMV model"
                            );
                        }
                    };
                }
            }

            // Base case: must be variable or predicate
            // println!("{}", s);
            if let Some(dyn_val) = smv_env.variables.get(s) {
                match dyn_val.sort {
                    VarType::Bool { .. }    => to_dyn!(bool_var!(state, s)),
                    VarType::Int { .. }     => to_dyn!(int_var!(state, s)),
                    VarType::BVector { .. } => to_dyn!(bv_var!(state, s)),
                }
            } else if let Some(pred_fn) = smv_env.predicates.get(s) {
                Dynamic::from(pred_fn(smv_env, ctx, state))
            } else {
                panic!("Unknown variable or predicate '{}', please make sure all variables are declared in INIT section.", s);
            }
        }

        recurse(smv_env, &var_name, &raw, ctx, state)
         
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
// fn run_nuxmv(commands_file: &str) -> io::Result<String> {
//     println!("running nuXmv");
//     // Command::new("/full/path/to/nuxmv")
//     let output = Command::new("/Users/milad/Desktop/rust_tutorial/HyperRUSTY/nuXmv")
//         .arg("-source")
//         .arg(commands_file)
//         .stdout(Stdio::piped())
//         .spawn()?
//         .wait_with_output()?;

//     if output.status.success() {
//         //DEBUG
//         // let result = String::from_utf8_lossy(&output.stdout).to_string();
//         // Ok(result)
//         Ok("success".to_string())
//     } else {
//         let error = String::from_utf8_lossy(&output.stderr).to_string();
//         Err(io::Error::new(io::ErrorKind::Other, error))
//     }
// }

/// Reads and parses the input file according to the given arguments, returning the output as a SMVEnv<'ctx>.
pub fn parse_smv<'ctx>(
    ctx: &'ctx Context,
    input_path: &str,
    output_path: Option<String>,
    bit_encode: bool,
    input_format: &str,
    output_format: &str,
) -> SMVEnv<'ctx>  {
    
    // println!("Parsing: {}\n", input_path);

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
                // println!("{}", output);
            }
            panic!("Expected output format 'ir' to return SMVEnv, but got 'primed'");
        }
        "functions" => {
            let output = generate_format_functions(&transitions);
            if let Some(out_path) = output_path {
                std::fs::write(&out_path, &output).expect("Failed to write output file");
            } else {
                // println!("{}", output);
            }
            panic!("Expected output format 'ir' to return SMVEnv, but got 'functions'");
        }
        "ir" => {
            // let cfg = z3::Config::new();
            // let ctx = Box::new(z3::Context::new(&cfg)); // owns the context
            let parsed_model = parse_original_smv(&content);

            // Leak the Box to give it a `'static` lifetime
            // let leaked_ctx: &'static z3::Context = Box::leak(ctx);

            generate_smv_env_from_parsed(ctx, parsed_model)
        }
        other => panic!("Unknown output format: {}", other),
    }
}











#[derive(Clone, Debug)]
struct Module {
    name: String,
    formals: Vec<String>,        // e.g., ["x","y"]
    body: String,                // full text of the module body
    vars: Vec<(String, String)>, // (name, sort)  sort is "boolean" or "lo..hi" (raw)
    defines: Vec<(String, String)>, // (lhs, rhs)
    inits: Vec<(String, String)>,   // init(var) := expr;
    nexts: Vec<(String, String)>,   // next(var) := expr;
}

/// Top-level flattening entry: returns a flattened NuSMV (single MODULE main).
pub fn flatten_nusmv(input: &str) -> String {
    // 1) Parse modules
    let modules = parse_modules(input);

    // 2) Find main
    let main = modules.get("main").unwrap_or_else(|| {
        panic!("No MODULE main found");
    });

    // 3) In main, collect:
    //    - its own base VAR/DEFINE/ASSIGN (non-instantiations)
    //    - all instantiations: inst_name : ModName(actuals...)
    let inst_re = Regex::new(r"(?m)^\s*([A-Za-z_]\w*)\s*:\s*([A-Za-z_]\w*)\s*\(([^)]*)\)\s*;").unwrap();
    // simple var decl (non-instance) inside main
    let simple_var_re = Regex::new(r"(?m)^\s*([\w.\[\]]+)\s*:\s*([A-Za-z_]\w*|[0-9]+\.\.[0-9]+)\s*;").unwrap();

    // Extract blocks from main
    let main_vars_block = extract_block(&main.body, "VAR");
    let main_def_block  = extract_block(&main.body, "DEFINE");
    let main_ass_block  = extract_block(&main.body, "ASSIGN");

    // Parse main non-instantiation vars
    let mut flat_vars: BTreeMap<String, String> = BTreeMap::new(); // name->sort
    for cap in simple_var_re.captures_iter(&main_vars_block) {
        let lhs = cap[1].trim();
        let rhs = cap[2].trim();
        // skip lines that are actually instantiations (we’ll add those separately)
        if inst_re.is_match(&cap[0]) { continue; }
        let lname = sanitize(lhs);
        flat_vars.insert(lname.clone(), rhs.to_string());
    }

    // Parse main DEFINE/ASSIGN (keep, just sanitize names + dotted refs)
    let parsed_main_defines = parse_defines(&main_def_block);
    let parsed_main_inits   = parse_inits(&main_ass_block);
    let parsed_main_nexts   = parse_nexts(&main_ass_block);

    // 4) Process each instantiation line in main VAR
    let mut flat_defines: Vec<(String, String)> = parsed_main_defines
        .into_iter()
        .map(|(l, r)| (sanitize(&l), rewrite_expr(&r, &HashMap::new())))
        .collect();

    let mut flat_inits: Vec<(String, String)> = parsed_main_inits
        .into_iter()
        .map(|(l, r)| (sanitize(&l), rewrite_expr(&r, &HashMap::new())))
        .collect();

    let mut flat_nexts: Vec<(String, String)> = parsed_main_nexts
        .into_iter()
        .map(|(l, r)| (sanitize(&l), rewrite_expr(&r, &HashMap::new())))
        .collect();

    for cap in inst_re.captures_iter(&main_vars_block) {
        let inst_name   = cap[1].trim().to_string();      // e.g., proc1
        let module_name = cap[2].trim().to_string();      // e.g., Proc
        let actuals_str = cap[3].trim();                  // e.g., a, b

        let module = modules.get(&module_name.to_lowercase()).unwrap_or_else(|| {
            panic!("Unknown module {} used by instance {}", module_name, inst_name);
        });

        // Build formal→actual map (sanitized)
        let actuals: Vec<String> = if actuals_str.is_empty() {
            vec![]
        } else {
            actuals_str.split(',')
                .map(|s| sanitize(s.trim()))
                .collect()
        };
        if actuals.len() != module.formals.len() {
            panic!("Instance {} : {} expects {} params but got {}",
                   inst_name, module_name, module.formals.len(), actuals.len());
        }
        let mut subst: HashMap<String, String> = HashMap::new();
        for (f, a) in module.formals.iter().zip(actuals.iter()) {
            subst.insert(f.clone(), a.clone());
        }

        // 4a) bring over vars with inst_ prefix
        for (v, sort) in &module.vars {
            let flat_name = format!("{}_{}", inst_name, sanitize(v));
            flat_vars.insert(flat_name, sort.clone());
        }

        // 4b) bring over defines
        for (lhs, rhs) in &module.defines {
            let lhs_flat = format!("{}_{}", inst_name, sanitize(lhs));
            let rhs_flat = rewrite_with_ctx(rhs, &inst_name, &module.vars, &subst);
            flat_defines.push((lhs_flat, rhs_flat));
        }

        // 4c) bring over ASSIGN init/next
        for (lhs, rhs) in &module.inits {
            let lhs_flat = format!("{}_{}", inst_name, sanitize(lhs));
            let rhs_flat = rewrite_with_ctx(rhs, &inst_name, &module.vars, &subst);
            flat_inits.push((lhs_flat, rhs_flat));
        }
        for (lhs, rhs) in &module.nexts {
            let lhs_flat = format!("{}_{}", inst_name, sanitize(lhs));
            let rhs_flat = rewrite_with_ctx(rhs, &inst_name, &module.vars, &subst);
            flat_nexts.push((lhs_flat, rhs_flat));
        }
    }

    // 5) Emit flattened main
    let mut out = String::new();
    out.push_str("MODULE main\n\n");

    // VAR
    out.push_str("VAR\n");
    for (name, sort) in &flat_vars {
        out.push_str(&format!("  {} : {};\n", name, sort));
    }
    out.push('\n');

    // DEFINE
    if !flat_defines.is_empty() {
        out.push_str("DEFINE\n");
        for (lhs, rhs) in &flat_defines {
            out.push_str(&format!("  {} := {};\n", lhs, rhs));
        }
        out.push('\n');
    }

    // ASSIGN
    if !flat_inits.is_empty() || !flat_nexts.is_empty() {
        out.push_str("ASSIGN\n");
        for (lhs, rhs) in &flat_inits {
            out.push_str(&format!("  init({}) := {};\n", lhs, rhs));
        }
        for (lhs, rhs) in &flat_nexts {
            out.push_str(&format!("  next({}) := {};\n", lhs, rhs));
        }
        out.push('\n');
    }

    out
}

/* ----------------- parsing helpers ----------------- */

fn parse_modules(input: &str) -> HashMap<String, Module> {
    // Capture MODULE name (optionally with params) + body up to next MODULE or EOF
    let mod_re = Regex::new(r"(?s)MODULE\s+([A-Za-z_]\w*)\s*(?:\(([^)]*)\))?\s*(.*?)(?=^\s*MODULE\s+[A-Za-z_]\w*|\z)").unwrap();

    let mut map = HashMap::<String, Module>::new();

    for cap in mod_re.captures_iter(input) {
        let name = cap[1].to_string();
        let params = cap.get(2).map(|m| m.as_str().trim()).unwrap_or("");
        let body = cap[3].to_string();

        let formals: Vec<String> = if params.is_empty() {
            vec![]
        } else {
            params.split(',').map(|s| sanitize(s.trim())).collect()
        };

        let vars = parse_vars(&body);
        let defines = parse_defines(&body);
        let inits = parse_inits(&body);
        let nexts = parse_nexts(&body);

        map.insert(
            name.to_lowercase(),
            Module { name, formals, body, vars, defines, inits, nexts },
        );
    }

    map
}

fn extract_block(body: &str, kw: &str) -> String {
    // grab the section between KW and the next top-level keyword (MODULE/VAR/DEFINE/ASSIGN/INIT/TRANS) or EOF
    let re = Regex::new(&format!(
        r"(?s)^\s*{}\b(.*?)(?=^\s*(MODULE|VAR|DEFINE|ASSIGN|INIT|TRANS)\b|\z)",
        regex::escape(kw)
    )).unwrap();
    if let Some(c) = re.captures(body) {
        c.get(1).map(|m| m.as_str().to_string()).unwrap_or_default()
    } else {
        String::new()
    }
}

fn parse_vars(body: &str) -> Vec<(String, String)> {
    let block = extract_block(body, "VAR");
    let var_decl_re = Regex::new(r"(?m)^\s*([\w.\[\]]+)\s*:\s*([A-Za-z_]\w*|[0-9]+\.\.[0-9]+)\s*;").unwrap();
    var_decl_re
        .captures_iter(&block)
        .map(|cap| (cap[1].trim().to_string(), cap[2].trim().to_string()))
        .collect()
}

fn parse_defines(body: &str) -> Vec<(String, String)> {
    let block = extract_block(body, "DEFINE");
    let define_re = Regex::new(r"(?m)^\s*([\w.\[\]]+)\s*:=\s*(.+?)\s*;").unwrap();
    define_re
        .captures_iter(&block)
        .map(|c| (c[1].trim().to_string(), c[2].trim().to_string()))
        .collect()
}

fn parse_inits(body: &str) -> Vec<(String, String)> {
    let block = extract_block(body, "ASSIGN"); // INIT often lives in ASSIGN block via init(x) :=
    let init_re = Regex::new(r"(?m)^\s*init\(([\w.\[\]]+)\)\s*:=\s*(.+?)\s*;").unwrap();
    init_re
        .captures_iter(&block)
        .map(|c| (c[1].trim().to_string(), c[2].trim().to_string()))
        .collect()
}

fn parse_nexts(body: &str) -> Vec<(String, String)> {
    let block = extract_block(body, "ASSIGN");
    let next_re = Regex::new(r"(?m)^\s*next\(([\w.\[\]]+)\)\s*:=\s*(.+?)\s*;").unwrap();
    next_re
        .captures_iter(&block)
        .map(|c| (c[1].trim().to_string(), c[2].trim().to_string()))
        .collect()
}

/* ----------------- rewriting helpers ----------------- */

fn sanitize(s: &str) -> String {
    // NuSMV allows dots in names; we flatten them with underscores.
    s.replace('.', "_")
}

/// Rewrite an expression with only dotted-name → underscored-name cleaning.
fn rewrite_expr(expr: &str, extra_map: &HashMap<String, String>) -> String {
    // Replace identifiers by sanitizing and optional substitution
    let id_re = Regex::new(r"(?x)
        (?P<kw>next|init)
        \s*\(
            (?P<inside>[^)]+)
        \)
        |
        (?P<ident>\b[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*\b)
    ").unwrap();

    id_re.replace_all(expr, |caps: &regex::Captures| {
        if let Some(m) = caps.name("kw") {
            // next(...) or init(...)
            let kw = m.as_str();
            let inside = caps.name("inside").unwrap().as_str();
            let cleaned_inside = rewrite_expr(inside, extra_map);
            format!("{kw}({cleaned_inside})")
        } else if let Some(id) = caps.name("ident") {
            let raw = id.as_str();
            let candidate = sanitize(raw);
            extra_map.get(&candidate).cloned().unwrap_or(candidate)
        } else {
            // shouldn't happen
            caps.get(0).unwrap().as_str().to_string()
        }
    }).to_string()
}

/// Rewrite using module-local context:
/// - local var `v` → `inst_v`
/// - formal `x`    → actual
/// - sanitize dotted names everywhere.
/// Also handles nested next()/init() arguments.
fn rewrite_with_ctx(
    expr: &str,
    inst: &str,
    mod_locals: &[(String, String)],
    formal_to_actual: &HashMap<String, String>,
) -> String {
    // Build a map for quick local var detection (sanitized)
    let mut locals: HashMap<String, String> = HashMap::new();
    for (v, _) in mod_locals {
        let v_clean = sanitize(v);
        locals.insert(v_clean.clone(), format!("{}_{}", inst, v_clean));
    }

    // Combined map (formals first, then locals)
    let mut extra = formal_to_actual.clone();
    extra.extend(locals);

    rewrite_expr(expr, &extra)
}

/* ----------------- Example ----------------- */

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flatten_simple() {
        let src = r#"
MODULE main
VAR
  proc1 : Proc(a, b);
  proc2 : Proc(a, b);
  a : 0..3;
  b : boolean;
DEFINE
  alive := b;
ASSIGN
  init(a) := 0;
  next(a) := a + 1;

MODULE Proc(x, y)
VAR
  line : 0..8;
  flag : boolean;
DEFINE
  good := (flag & y);
ASSIGN
  init(line) := 0;
  next(line) := x + 1;
  next(flag) := !flag;
"#;

        let flat = flatten_nusmv(src);
        // println!("{flat}");
        assert!(flat.contains("MODULE main"));
        assert!(flat.contains("proc1_line : 0..8;"));
        assert!(flat.contains("proc2_flag : boolean;"));
        assert!(flat.contains("init(proc1_line) := 0;"));
        assert!(flat.contains("next(proc2_line) := a + 1;")); // x→a substitution
    }
}