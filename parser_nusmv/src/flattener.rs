use regex::Regex;
use std::collections::{BTreeMap, HashMap};

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
        println!("{flat}");
        assert!(flat.contains("MODULE main"));
        assert!(flat.contains("proc1_line : 0..8;"));
        assert!(flat.contains("proc2_flag : boolean;"));
        assert!(flat.contains("init(proc1_line) := 0;"));
        assert!(flat.contains("next(proc2_line) := a + 1;")); // x→a substitution
    }
}