// yosys_smt2_flatten_inline.rs
// Flatten a Yosys SMT-LIBv2 file by:
//  1) Removing the state datatype usage (no record-typed 'state').
//  2) Declaring constants for each state field.
//  3) Defining ONE transition function per state field, fully inlined.
//  4) Defining zero-arity |init <FIELD>| functions ONLY for fields constrained by |<top>_i|.
//  5) No helper constants and NO (assert ...) are emitted.
//
// This version implements a GLOBAL pre-inlining cache for helper define-funs,
// so each helper is fully inlined exactly once and reused across all fields.

use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::io;

#[derive(Clone, Debug, PartialEq, Eq)]
enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

fn atom<S: Into<String>>(s: S) -> SExpr {
    SExpr::Atom(s.into())
}
fn list(v: Vec<SExpr>) -> SExpr {
    SExpr::List(v)
}

fn strip_comments(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for mut line in text.lines() {
        if let Some(idx) = line.find(';') {
            line = &line[..idx];
        }
        out.push_str(line);
        out.push('\n');
    }
    out
}

fn tokenize(text: &str) -> Vec<String> {
    let mut t = Vec::<String>::new();
    let mut i = 0usize;
    let b = text.as_bytes();
    let n = b.len();
    while i < n {
        let c = b[i] as char;
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == '(' || c == ')' {
            t.push(c.to_string());
            i += 1;
            continue;
        }
        if c == '|' {
            // pipe-quoted symbol
            let mut j = i + 1;
            while j < n && b[j] as char != '|' {
                j += 1;
            }
            if j >= n {
                panic!("Unterminated |...| symbol");
            }
            let s = &text[i..=j];
            t.push(s.to_string());
            i = j + 1;
            continue;
        }
        // normal atom
        let mut j = i;
        while j < n {
            let cj = b[j] as char;
            if cj.is_whitespace() || cj == '(' || cj == ')' {
                break;
            }
            j += 1;
        }
        t.push(text[i..j].to_string());
        i = j;
    }
    t
}

fn parse_sexprs(tokens: &[String]) -> Vec<SExpr> {
    fn parse_one(tokens: &[String], i: &mut usize) -> SExpr {
        if *i >= tokens.len() {
            panic!("Unexpected EOF in parse");
        }
        let t = &tokens[*i];
        *i += 1;
        if t == "(" {
            let mut v = Vec::<SExpr>::new();
            loop {
                if *i >= tokens.len() {
                    panic!("Unmatched '('");
                }
                if tokens[*i] == ")" {
                    *i += 1;
                    break;
                }
                v.push(parse_one(tokens, i));
            }
            SExpr::List(v)
        } else if t == ")" {
            panic!("Unexpected ')'");
        } else {
            SExpr::Atom(t.clone())
        }
    }
    let mut i = 0usize;
    let mut out = Vec::<SExpr>::new();
    while i < tokens.len() {
        out.push(parse_one(tokens, &mut i));
    }
    out
}

fn sexpr_to_string(x: &SExpr) -> String {
    match x {
        SExpr::Atom(s) => s.clone(),
        SExpr::List(v) => {
            let mut s = String::from("(");
            let mut first = true;
            for e in v {
                if !first {
                    s.push(' ');
                }
                first = false;
                s.push_str(&sexpr_to_string(e));
            }
            s.push(')');
            s
        }
    }
}

#[derive(Clone, Debug)]
struct Sort {
    ast: SExpr,
}
impl Sort {
    fn to_string(&self) -> String {
        sexpr_to_string(&self.ast)
    }
}

#[derive(Clone, Debug)]
struct FunDef {
    name: String,
    params: Vec<(String, Sort)>,
    ret: Sort,
    body: SExpr,
}

#[derive(Clone, Debug)]
struct ModuleState {
    sort_symbol: String,
    ctor: String,
    fields: Vec<(String, Sort)>, // (field_name, sort)
}

#[derive(Clone, Debug)]
struct ModelIR {
    module: Option<ModuleState>,
    funs: HashMap<String, FunDef>,
}

fn parse_sort(ast: SExpr) -> Sort {
    Sort { ast }
}

fn parse_fun_def(ast: &SExpr) -> FunDef {
    // (define-fun name ((p s) ...) ret body)
    let l = match ast {
        SExpr::List(v) => v,
        _ => panic!("define-fun not a list"),
    };
    assert!(l.len() >= 5 && matches!(&l[0], SExpr::Atom(a) if a=="define-fun"));
    let name = match &l[1] {
        SExpr::Atom(s) => s.clone(),
        _ => panic!("fun name must be atom"),
    };
    let params_ast = match &l[2] {
        SExpr::List(v) => v,
        _ => panic!("params must be list"),
    };
    let mut params = Vec::<(String, Sort)>::new();
    for p in params_ast {
        match p {
            SExpr::List(pp) if pp.len() == 2 => {
                let pn = match &pp[0] {
                    SExpr::Atom(s) => s.clone(),
                    _ => panic!("param name must be atom"),
                };
                let psort = parse_sort(pp[1].clone());
                params.push((pn, psort));
            }
            _ => panic!("param entry invalid"),
        }
    }
    let ret = parse_sort(l[3].clone());
    let body = l[4].clone();
    FunDef { name, params, ret, body }
}

fn parse_declare_datatype(ast: &SExpr) -> ModuleState {
    // (declare-datatype |mod_s| ((|ctor| (|field| sort) ... )))
    let l = match ast {
        SExpr::List(v) => v,
        _ => panic!("declare-datatype not a list"),
    };
    assert!(l.len() >= 3 && matches!(&l[0], SExpr::Atom(a) if a=="declare-datatype"));
    let sort_symbol = match &l[1] {
        SExpr::Atom(s) => s.clone(),
        _ => panic!("sort symbol must be atom"),
    };
    let ctors = match &l[2] {
        SExpr::List(v) => v,
        _ => panic!("ctors must be list"),
    };
    assert!(ctors.len() == 1);
    let ctor = match &ctors[0] {
        SExpr::List(v) => v,
        _ => panic!("ctor not list"),
    };
    assert!(!ctor.is_empty());
    let ctor_name = match &ctor[0] {
        SExpr::Atom(s) => s.clone(),
        _ => panic!("ctor name must be atom"),
    };
    let mut fields = Vec::<(String, Sort)>::new();
    for f in &ctor[1..] {
        match f {
            SExpr::List(ff) if ff.len() == 2 => {
                let fname = match &ff[0] {
                    SExpr::Atom(s) => s.clone(),
                    _ => panic!("field name must be atom"),
                };
                let fsort = parse_sort(ff[1].clone());
                fields.push((fname, fsort));
            }
            _ => panic!("field entry invalid"),
        }
    }
    ModuleState { sort_symbol, ctor: ctor_name, fields }
}

fn load_model_ir(text: &str) -> ModelIR {
    let stripped = strip_comments(text);
    let tokens = tokenize(&stripped);
    let sexprs = parse_sexprs(&tokens);
    let mut module = None::<ModuleState>;
    let mut funs = HashMap::<String, FunDef>::new();
    for node in sexprs {
        if let SExpr::List(v) = &node {
            if !v.is_empty() {
                if let SExpr::Atom(tag) = &v[0] {
                    if tag == "declare-datatype" {
                        module = Some(parse_declare_datatype(&node));
                        continue;
                    } else if tag == "define-fun" {
                        let f = parse_fun_def(&node);
                        funs.insert(f.name.clone(), f);
                        continue;
                    }
                }
            }
        }
    }
    ModelIR { module, funs }
}

// ---------- utilities for names/quoting ----------

fn strip_pipes(s: &str) -> &str {
    if s.len() >= 2 && s.starts_with('|') && s.ends_with('|') {
        &s[1..s.len() - 1]
    } else {
        s
    }
}
fn add_pipes(s: &str) -> String {
    format!("|{}|", s)
}
fn modname_from_sort(sort_symbol: &str) -> String {
    let core = strip_pipes(sort_symbol);
    if core.ends_with("_s") {
        core[..core.len() - 2].to_string()
    } else {
        core.to_string()
    }
}
fn name_endswith(sym: &str, suffix: &str) -> bool {
    strip_pipes(sym).ends_with(suffix)
}
fn sort_is_state(s: &Sort, state_sort_symbol: &str) -> bool {
    matches!(&s.ast, SExpr::Atom(a) if a == state_sort_symbol)
}

// ---------- find transition / init ----------

fn find_transition_fun(ir: &ModelIR) -> Option<FunDef> {
    let module = ir.module.as_ref()?;
    let state_sort = &module.sort_symbol;
    let modname = modname_from_sort(state_sort);
    let expect_q = add_pipes(&format!("{}_t", modname));
    let expect_u = format!("{}_t", modname);

    // exact match first
    for f in ir.funs.values() {
        if (f.name == expect_q || f.name == expect_u)
            && f.params.len() == 2
            && sort_is_state(&f.params[0].1, state_sort)
            && sort_is_state(&f.params[1].1, state_sort)
        {
            return Some(f.clone());
        }
    }
    // suffix match
    for f in ir.funs.values() {
        if name_endswith(&f.name, "_t")
            && f.params.len() == 2
            && sort_is_state(&f.params[0].1, state_sort)
            && sort_is_state(&f.params[1].1, state_sort)
        {
            return Some(f.clone());
        }
    }
    // fallback
    for f in ir.funs.values() {
        if f.params.len() == 2
            && sort_is_state(&f.params[0].1, state_sort)
            && sort_is_state(&f.params[1].1, state_sort)
        {
            return Some(f.clone());
        }
    }
    None
}

fn find_init_fun(ir: &ModelIR) -> Option<FunDef> {
    let module = ir.module.as_ref()?;
    let state_sort = &module.sort_symbol;
    let modname = modname_from_sort(state_sort);
    let expect_q = add_pipes(&format!("{}_i", modname));
    let expect_u = format!("{}_i", modname);

    // exact name first
    for f in ir.funs.values() {
        if (f.name == expect_q || f.name == expect_u)
            && f.params.len() == 1
            && sort_is_state(&f.params[0].1, state_sort)
        {
            return Some(f.clone());
        }
    }
    // suffix fallback
    for f in ir.funs.values() {
        if name_endswith(&f.name, "_i")
            && f.params.len() == 1
            && sort_is_state(&f.params[0].1, state_sort)
        {
            return Some(f.clone());
        }
    }
    // last resort: any single-arg Bool predicate over state sort
    for f in ir.funs.values() {
        if f.params.len() == 1
            && sort_is_state(&f.params[0].1, state_sort)
            && matches!(&f.ret.ast, SExpr::Atom(b) if b=="Bool")
        {
            return Some(f.clone());
        }
    }
    None
}

// ---------- AND flattener ----------

fn flatten_and(expr: &SExpr) -> Vec<SExpr> {
    if let SExpr::List(v) = expr {
        if !v.is_empty() {
            if let SExpr::Atom(tag) = &v[0] {
                if tag == "and" {
                    let mut out = Vec::<SExpr>::new();
                    for e in &v[1..] {
                        out.extend(flatten_and(e));
                    }
                    return out;
                }
            }
        }
    }
    vec![expr.clone()]
}

// ---------- collect per-field next exprs ----------

fn collect_assignments_from_t(f_t: &FunDef, module: &ModuleState) -> HashMap<String, SExpr> {
    let next_var = &f_t.params[1].0;
    let conjuncts = flatten_and(&f_t.body);
    let rhs_selectors: HashSet<String> =
        module.fields.iter().map(|(f, _)| f.clone()).collect();
    let mut mapping = HashMap::<String, SExpr>::new();

    for c in conjuncts {
        if let SExpr::List(v) = &c {
            if v.len() == 3 {
                if let SExpr::Atom(eq) = &v[0] {
                    if eq == "=" {
                        let lhs = v[1].clone();
                        let rhs = v[2].clone();
                        if let SExpr::List(r) = &rhs {
                            if r.len() == 2 {
                                if let (SExpr::Atom(fsel), SExpr::Atom(nv)) = (&r[0], &r[1]) {
                                    if rhs_selectors.contains(fsel) && nv == next_var {
                                        mapping.insert(fsel.clone(), lhs);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    mapping
}

// ---------- GLOBAL PRE-INLINING OF HELPERS (Suggestion 1) ----------

/// Build once: fully inlined body for each helper F(state) where F is unary on the module state.
/// Selector calls (|FIELD| state_param) become bare |FIELD|.
/// Helper calls (G state_param) become the fully inlined body of G.
fn preinline_helpers(ir: &ModelIR, module: &ModuleState) -> HashMap<String, SExpr> {
    let selector_names: HashSet<String> =
        module.fields.iter().map(|(f, _)| f.clone()).collect();

    let helpers: HashMap<String, FunDef> = ir
        .funs
        .iter()
        .filter_map(|(name, f)| {
            if f.params.len() == 1 && sort_is_state(&f.params[0].1, &module.sort_symbol) {
                Some((name.clone(), f.clone()))
            } else {
                None
            }
        })
        .collect();

    let mut done = HashMap::<String, SExpr>::new();
    let mut visiting = HashSet::<String>::new();

    fn rewrite_with_state(
        e: &SExpr,
        s_var: &str,
        selector_names: &HashSet<String>,
        helpers: &HashMap<String, FunDef>,
        done: &mut HashMap<String, SExpr>,
        visiting: &mut HashSet<String>,
    ) -> SExpr {
        match e {
            SExpr::Atom(_) => e.clone(),
            SExpr::List(v) if v.len() == 2 => {
                if let (SExpr::Atom(h), SExpr::Atom(arg)) = (&v[0], &v[1]) {
                    // (|FIELD| s_var) -> |FIELD|
                    if selector_names.contains(h) && arg == s_var {
                        return atom(h.clone());
                    }
                    // (F s_var) -> inline F via precompute
                    if let Some(fdef) = helpers.get(h) {
                        if arg == s_var {
                            // compute F if needed
                            if let Some(cached) = done.get(h) {
                                return cached.clone();
                            }
                            if !visiting.insert(h.clone()) {
                                // cycle guard; shouldn't happen in Yosys
                                return SExpr::List(v.clone());
                            }
                            let param_name = &fdef.params[0].0;
                            let body = rewrite_with_state(
                                &fdef.body,
                                param_name,
                                selector_names,
                                helpers,
                                done,
                                visiting,
                            );
                            visiting.remove(h);
                            done.insert(h.clone(), body.clone());
                            return body;
                        }
                    }
                }
                // generic recursion
                SExpr::List(
                    v.iter()
                        .map(|a| rewrite_with_state(a, s_var, selector_names, helpers, done, visiting))
                        .collect(),
                )
            }
            SExpr::List(v) => SExpr::List(
                v.iter()
                    .map(|a| rewrite_with_state(a, s_var, selector_names, helpers, done, visiting))
                    .collect(),
            ),
        }
    }

    // Precompute each helper's inlined body with respect to its own param.
    for (name, f) in &helpers {
        if !done.contains_key(name) {
            let param_name = &f.params[0].0;
            let body = rewrite_with_state(
                &f.body,
                param_name,
                &selector_names,
                &helpers,
                &mut done,
                &mut visiting,
            );
            done.insert(name.clone(), body);
        }
    }
    done
}

/// Use the pre-inlined helper map to inline helpers in `expr` with respect to `state_var`,
/// and still replace (|FIELD| state_var) -> |FIELD|.
fn rewrite_expr_inline_using_pre(
    module: &ModuleState,
    expr: &SExpr,
    state_var: &str,
    pre: &HashMap<String, SExpr>,
) -> SExpr {
    let selector_names: HashSet<String> =
        module.fields.iter().map(|(f, _)| f.clone()).collect();

    fn walk(
        e: &SExpr,
        s: &str,
        selectors: &HashSet<String>,
        pre: &HashMap<String, SExpr>,
    ) -> SExpr {
        match e {
            SExpr::Atom(_) => e.clone(),
            SExpr::List(v) if v.len() == 2 => {
                if let (SExpr::Atom(h), SExpr::Atom(arg)) = (&v[0], &v[1]) {
                    if selectors.contains(h) && arg == s {
                        return atom(h.clone());
                    }
                    if arg == s {
                        if let Some(inlined) = pre.get(h) {
                            return inlined.clone();
                        }
                    }
                }
                SExpr::List(v.iter().map(|a| walk(a, s, selectors, pre)).collect())
            }
            SExpr::List(v) => SExpr::List(v.iter().map(|a| walk(a, s, selectors, pre)).collect()),
        }
    }

    walk(expr, state_var, &selector_names, pre)
}


// ---------- init extraction helpers ----------

fn sort_is_bv1(s: &Sort) -> bool {
    match &s.ast {
        SExpr::List(v) if v.len() == 3 => {
            matches!(&v[0], SExpr::Atom(a) if a=="_")
                && matches!(&v[1], SExpr::Atom(a) if a=="BitVec")
                && matches!(&v[2], SExpr::Atom(a) if a=="1")
        }
        _ => false,
    }
}
fn is_true(x: &SExpr) -> bool {
    matches!(x, SExpr::Atom(a) if a=="true")
}
fn is_false(x: &SExpr) -> bool {
    matches!(x, SExpr::Atom(a) if a=="false")
}
fn as_eq(x: &SExpr) -> Option<(SExpr, SExpr)> {
    if let SExpr::List(v) = x {
        if v.len() == 3 {
            if let SExpr::Atom(eq) = &v[0] {
                if eq == "=" {
                    return Some((v[1].clone(), v[2].clone()));
                }
            }
        }
    }
    None
}

// Match ((_ extract 0 0) |FIELD|)
fn extract00_field(term: &SExpr) -> Option<String> {
    if let SExpr::List(v) = term {
        if v.len() == 2 {
            if let (SExpr::List(head), SExpr::Atom(arg)) = (&v[0], &v[1]) {
                if head.len() >= 4 {
                    let h0 = match &head[0] {
                        SExpr::Atom(s) => s.as_str(),
                        _ => "",
                    };
                    let h1 = match &head[1] {
                        SExpr::Atom(s) => s.as_str(),
                        _ => "",
                    };
                    let h2 = match &head[2] {
                        SExpr::Atom(s) => s.as_str(),
                        _ => "",
                    };
                    let h3 = match &head[3] {
                        SExpr::Atom(s) => s.as_str(),
                        _ => "",
                    };
                    if (h0 == "(_" || h0 == "_") && h1 == "extract" && h2 == "0" && h3 == "0" {
                        return Some(arg.clone());
                    }
                }
            }
        }
    }
    None
}

fn bv1_from_bool_constraint(inner_eq: &SExpr, truth: bool) -> Option<(String, String)> {
    let (a, b) = as_eq(inner_eq)?;
    // Case 1: (= ((_ extract 0 0) FIELD) #b{0,1})
    if let Some(fld) = extract00_field(&a) {
        if let SExpr::Atom(bit) = &b {
            if bit == "#b0" || bit == "#b1" {
                let want_one = bit == "#b1";
                let final_bit = if want_one == truth { "#b1" } else { "#b0" };
                return Some((fld, final_bit.to_string()));
            }
        }
    }
    // Case 2: (= #b{0,1} ((_ extract 0 0) FIELD))
    if let Some(fld) = extract00_field(&b) {
        if let SExpr::Atom(bit) = &a {
            if bit == "#b0" || bit == "#b1" {
                let want_one = bit == "#b1";
                let final_bit = if want_one == truth { "#b1" } else { "#b0" };
                return Some((fld, final_bit.to_string()));
            }
        }
    }
    None
}

fn extract_init_values(
    ir: &ModelIR,
    module: &ModuleState,
    init_fun: &FunDef,
    pre: &HashMap<String, SExpr>,
) -> HashMap<String, SExpr> {
    let state_var = &init_fun.params[0].0;
    // Use pre-inlined helpers:
    let inlined = rewrite_expr_inline_using_pre(module, &init_fun.body, state_var, pre);
    let conjuncts = flatten_and(&inlined);
    let field_sorts: HashMap<String, Sort> = module
        .fields
        .iter()
        .map(|(f, s)| (f.clone(), s.clone()))
        .collect();

    let mut values = HashMap::<String, SExpr>::new();

    for c in conjuncts {
        if let Some((a, b)) = as_eq(&c) {
            // direct equality
            if let SExpr::Atom(sa) = &a {
                if field_sorts.contains_key(sa) {
                    values.entry(sa.clone()).or_insert(b.clone());
                    continue;
                }
            }
            if let SExpr::Atom(sb) = &b {
                if field_sorts.contains_key(sb) {
                    values.entry(sb.clone()).or_insert(a.clone());
                    continue;
                }
            }
            // booleanized BV1: (= inner true/false) in any order
            let (inner, truth) = if is_true(&a) || is_false(&a) {
                (b.clone(), is_true(&a))
            } else if is_true(&b) || is_false(&b) {
                (a.clone(), is_true(&b))
            } else {
                (atom(""), false)
            };
            if let SExpr::Atom(dummy) = &inner {
                if dummy.is_empty() {
                    continue;
                }
            }
            if let Some((fld, lit)) = bv1_from_bool_constraint(&inner, truth) {
                if let Some(srt) = field_sorts.get(&fld) {
                    if sort_is_bv1(srt) {
                        values.entry(fld).or_insert(atom(lit));
                    }
                }
            }
        }
    }
    values
}

// ---------- transform ----------

fn render_sort(s: &Sort) -> String {
    s.to_string()
}
fn render_decl_const(name: &str, sort: &Sort) -> String {
    format!("(declare-const {} {})", name, render_sort(sort))
}
fn render_define_fun(
    name: &str,
    params: &Vec<(String, Sort)>,
    ret: &Sort,
    body: &SExpr,
) -> String {
    let mut ps = String::new();
    let mut first = true;
    for (pn, psort) in params {
        if !first {
            ps.push(' ');
        }
        first = false;
        ps.push('(');
        ps.push_str(pn);
        ps.push(' ');
        ps.push_str(&render_sort(psort));
        ps.push(')');
    }
    format!(
        "(define-fun {} ({}) {} {})",
        name,
        ps,
        render_sort(ret),
        sexpr_to_string(body)
    )
}

pub fn transform(text: &str) -> String {
    let ir = load_model_ir(text);
    let module = ir.module.as_ref().expect("No module/state datatype found.");
    let f_t = find_transition_fun(&ir).expect("No transition function found.");
    let next_map = collect_assignments_from_t(&f_t, module);
    let state_param_name = &f_t.params[0].0;

    // NEW: compute global pre-inlined helpers once.
    let pre = preinline_helpers(&ir, module);

    let init_values = if let Some(f_i) = find_init_fun(&ir) {
        extract_init_values(&ir, module, &f_i, &pre)
    } else {
        HashMap::new()
    };

    let mut out_lines = Vec::<String>::new();
    out_lines.push("; Flattened SMT-LIB (inline mode): no helper consts and no assertions.".into());
    out_lines.push("; Declares base state consts, defines per-field next functions (inline),".into());
    out_lines.push("; and per-field init functions inferred from |<top>_i| where possible.\n".into());

    // state field constants
    out_lines.push("; --- State field constants ---".into());
    for (fname, sort) in &module.fields {
        out_lines.push(render_decl_const(fname, sort));
    }
    out_lines.push("".into());

    // per-field next functions
    let params_all = module.fields.clone();
    out_lines.push("; --- Per-field transition functions (fully inlined) ---".into());
    for (field_name, field_sort) in &module.fields {
        if let Some(raw_expr) = next_map.get(field_name) {
            // Use the pre-inlined helpers here:
            let inlined = rewrite_expr_inline_using_pre(module, raw_expr, state_param_name, &pre);
            let fun_name = if field_name.starts_with('|') && field_name.ends_with('|') {
                add_pipes(&format!("next {}", &field_name[1..field_name.len()-1]))
            } else {
                format!("next_{}", field_name)
            };
            out_lines.push(render_define_fun(&fun_name, &params_all, field_sort, &inlined));
        }
    }
    out_lines.push("".into());

    // per-field init functions (only for constrained fields)
    out_lines.push("; --- Per-field initial value functions (only for constrained fields) ---".into());
    for (field_name, field_sort) in &module.fields {
        if let Some(body) = init_values.get(field_name) {
            let fname = if field_name.starts_with('|') && field_name.ends_with('|') {
                add_pipes(&format!("init {}", &field_name[1..field_name.len()-1]))
            } else {
                format!("init_{}", field_name)
            };
            out_lines.push(render_define_fun(&fname, &Vec::new(), field_sort, body));
        }
    }
    out_lines.push("".into());

    out_lines.join("\n")
}

// ---------- main ----------

fn main() -> io::Result<()> {
    let args: Vec<String> = env::args().collect();
    if !(args.len() == 3) {
        eprintln!(
            "Usage: {} <input.smt2> <output.smt2>",
            args.get(0).map(String::as_str).unwrap_or("smt_flatten")
        );
        std::process::exit(2);
    }
    let input = &args[1];
    let output = &args[2];
    let text = fs::read_to_string(input)?;
    let out = transform(&text);
    fs::write(output, out)?;
    println!("Wrote {}", output);
    Ok(())
}
