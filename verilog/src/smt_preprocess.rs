// yosys_smt2_flatten_helpers_min.rs
// Keep helpers as helper functions; remove state datatype.
// Each helper takes ONLY the fields it (transitively) uses.
// Next functions call helpers with those minimized parameter lists.
// Init functions are emitted for fields constrained by |<top>_i|.

use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::io;

// ---------------- SExpr ----------------

#[derive(Clone, Debug, PartialEq, Eq)]
enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}
fn atom<S: Into<String>>(s: S) -> SExpr { SExpr::Atom(s.into()) }
fn list(v: Vec<SExpr>) -> SExpr { SExpr::List(v) }

fn sexpr_to_string(x: &SExpr) -> String {
    match x {
        SExpr::Atom(s) => s.clone(),
        SExpr::List(v) => {
            let mut s = String::from("(");
            let mut first = true;
            for e in v {
                if !first { s.push(' '); }
                first = false;
                s.push_str(&sexpr_to_string(e));
            }
            s.push(')');
            s
        }
    }
}

// --------------- SMT-LIB parsing ---------------

fn strip_comments(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for mut line in text.lines() {
        if let Some(idx) = line.find(';') { line = &line[..idx]; }
        out.push_str(line);
        out.push('\n');
    }
    out
}

fn tokenize(text: &str) -> Vec<String> {
    let mut t = Vec::<String>::new();
    let b = text.as_bytes();
    let mut i = 0usize;
    while i < b.len() {
        let c = b[i] as char;
        if c.is_whitespace() { i += 1; continue; }
        if c == '(' || c == ')' { t.push(c.to_string()); i += 1; continue; }
        if c == '|' {
            let mut j = i + 1;
            while j < b.len() && b[j] as char != '|' { j += 1; }
            if j >= b.len() { panic!("Unterminated |...| symbol"); }
            t.push(text[i..=j].to_string());
            i = j + 1;
            continue;
        }
        let mut j = i;
        while j < b.len() {
            let cj = b[j] as char;
            if cj.is_whitespace() || cj == '(' || cj == ')' { break; }
            j += 1;
        }
        t.push(text[i..j].to_string());
        i = j;
    }
    t
}

fn parse_sexprs(tokens: &[String]) -> Vec<SExpr> {
    fn parse_one(tokens: &[String], i: &mut usize) -> SExpr {
        if *i >= tokens.len() { panic!("Unexpected EOF"); }
        let t = &tokens[*i]; *i += 1;
        if t == "(" {
            let mut v = Vec::<SExpr>::new();
            loop {
                if *i >= tokens.len() { panic!("Unmatched '('"); }
                if tokens[*i] == ")" { *i += 1; break; }
                v.push(parse_one(tokens, i));
            }
            SExpr::List(v)
        } else if t == ")" {
            panic!("Unexpected ')'");
        } else {
            SExpr::Atom(t.clone())
        }
    }
    let mut out = Vec::<SExpr>::new();
    let mut i = 0usize;
    while i < tokens.len() {
        out.push(parse_one(tokens, &mut i));
    }
    out
}

// ---------------- IR ----------------

#[derive(Clone, Debug)]
struct Sort { ast: SExpr }
impl Sort {
    fn to_string(&self) -> String { sexpr_to_string(&self.ast) }
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

fn parse_sort(ast: SExpr) -> Sort { Sort { ast } }

fn parse_fun_def(ast: &SExpr) -> FunDef {
    let l = match ast { SExpr::List(v) => v, _ => panic!("define-fun not a list") };
    assert!(l.len() >= 5 && matches!(&l[0], SExpr::Atom(a) if a=="define-fun"));
    let name = match &l[1] { SExpr::Atom(s)=>s.clone(), _=>panic!("fun name must be atom") };
    let params_ast = match &l[2] { SExpr::List(v)=>v, _=>panic!("params") };
    let mut params = Vec::<(String, Sort)>::new();
    for p in params_ast {
        match p {
            SExpr::List(pp) if pp.len()==2 => {
                let pn = match &pp[0] { SExpr::Atom(s)=>s.clone(), _=>panic!("param name") };
                let psort = parse_sort(pp[1].clone());
                params.push((pn, psort));
            }
            _ => panic!("param entry"),
        }
    }
    let ret = parse_sort(l[3].clone());
    let body = l[4].clone();
    FunDef { name, params, ret, body }
}

fn parse_declare_datatype(ast: &SExpr) -> ModuleState {
    // (declare-datatype |mod_s| ((|ctor| (|field| sort) ... )))
    let l = match ast { SExpr::List(v)=>v, _=>panic!("declare-datatype not a list") };
    assert!(l.len()>=3 && matches!(&l[0], SExpr::Atom(a) if a=="declare-datatype"));
    let sort_symbol = match &l[1] { SExpr::Atom(s)=>s.clone(), _=>panic!("sort sym") };
    let ctors = match &l[2] { SExpr::List(v)=>v, _=>panic!("ctors") };
    assert!(ctors.len()==1);
    let ctor = match &ctors[0] { SExpr::List(v)=>v, _=>panic!("ctor") };
    assert!(!ctor.is_empty());
    let ctor_name = match &ctor[0] { SExpr::Atom(s)=>s.clone(), _=>panic!("ctor name") };
    let mut fields = Vec::<(String, Sort)>::new();
    for f in &ctor[1..] {
        match f {
            SExpr::List(ff) if ff.len()==2 => {
                let fname = match &ff[0] { SExpr::Atom(s)=>s.clone(), _=>panic!("field name") };
                let fsort = parse_sort(ff[1].clone());
                fields.push((fname, fsort));
            }
            _ => panic!("field entry"),
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
            if v.is_empty() { continue; }
            if let SExpr::Atom(tag) = &v[0] {
                if tag == "declare-datatype" {
                    module = Some(parse_declare_datatype(&node));
                } else if tag == "define-fun" {
                    let f = parse_fun_def(&node);
                    funs.insert(f.name.clone(), f);
                }
            }
        }
    }
    ModelIR { module, funs }
}

// ---------------- utilities ----------------

fn strip_pipes(s: &str) -> &str {
    if s.len()>=2 && s.starts_with('|') && s.ends_with('|') { &s[1..s.len()-1] } else { s }
}
fn add_pipes(s: &str) -> String { format!("|{}|", s) }
fn modname_from_sort(sort_symbol: &str) -> String {
    let core = strip_pipes(sort_symbol);
    if core.ends_with("_s") { core[..core.len()-2].to_string() } else { core.to_string() }
}
fn sort_is_state(s: &Sort, state_sort_symbol: &str) -> bool {
    matches!(&s.ast, SExpr::Atom(a) if a==state_sort_symbol)
}
fn name_endswith(sym: &str, suffix: &str) -> bool {
    strip_pipes(sym).ends_with(suffix)
}

fn flatten_and(expr: &SExpr) -> Vec<SExpr> {
    if let SExpr::List(v) = expr {
        if !v.is_empty() {
            if let SExpr::Atom(a) = &v[0] {
                if a == "and" {
                    let mut out = Vec::<SExpr>::new();
                    for e in &v[1..] { out.extend(flatten_and(e)); }
                    return out;
                }
            }
        }
    }
    vec![expr.clone()]
}

// ---------------- find transition/init ----------------

fn find_transition_fun(ir: &ModelIR) -> Option<FunDef> {
    let module = ir.module.as_ref()?;
    let state_sort = &module.sort_symbol;
    let modname = modname_from_sort(state_sort);
    let expect_q = add_pipes(&format!("{}_t", modname));
    let expect_u = format!("{}_t", modname);
    for f in ir.funs.values() {
        if (f.name==expect_q || f.name==expect_u)
            && f.params.len()==2
            && sort_is_state(&f.params[0].1, state_sort)
            && sort_is_state(&f.params[1].1, state_sort) { return Some(f.clone()); }
    }
    for f in ir.funs.values() {
        if f.params.len()==2
            && sort_is_state(&f.params[0].1, state_sort)
            && sort_is_state(&f.params[1].1, state_sort) { return Some(f.clone()); }
    }
    None
}

fn find_init_fun(ir: &ModelIR) -> Option<FunDef> {
    let module = ir.module.as_ref()?;
    let state_sort = &module.sort_symbol;
    let modname = modname_from_sort(state_sort);
    let expect_q = add_pipes(&format!("{}_i", modname));
    let expect_u = format!("{}_i", modname);
    for f in ir.funs.values() {
        if (f.name==expect_q || f.name==expect_u)
            && f.params.len()==1
            && sort_is_state(&f.params[0].1, state_sort) { return Some(f.clone()); }
    }
    for f in ir.funs.values() {
        if f.params.len()==1
            && sort_is_state(&f.params[0].1, state_sort)
            && matches!(&f.ret.ast, SExpr::Atom(b) if b=="Bool") { return Some(f.clone()); }
    }
    None
}

// ---------------- collect next-assignments ----------------

fn collect_assignments_from_t(f_t: &FunDef, module: &ModuleState) -> HashMap<String, SExpr> {
    let next_var = &f_t.params[1].0;
    let conjuncts = flatten_and(&f_t.body);
    let rhs_selectors: HashSet<String> = module.fields.iter().map(|(f,_)| f.clone()).collect();
    let mut mapping = HashMap::<String, SExpr>::new();

    for c in conjuncts {
        if let SExpr::List(v) = &c {
            if v.len()==3 {
                if let SExpr::Atom(eq) = &v[0] {
                    if eq == "=" {
                        let lhs = v[1].clone();
                        let rhs = v[2].clone();
                        if let SExpr::List(r) = &rhs {
                            if r.len()==2 {
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

// =================== HELPERS WITH MIN PARAM LISTS ===================

fn collect_helpers(ir: &ModelIR, module: &ModuleState) -> HashMap<String, FunDef> {
    ir.funs.iter()
        .filter_map(|(n,f)| {
            if f.params.len()==1 && sort_is_state(&f.params[0].1, &module.sort_symbol) {
                Some((n.clone(), f.clone()))
            } else { None }
        })
        .collect()
}

/// Analyze direct usage of a helper: fields directly selected and helpers directly called.
fn analyze_helper_direct(
    f: &FunDef,
    module: &ModuleState,
    helper_names: &HashSet<String>,
) -> (HashSet<String>, HashSet<String>) {
    let state_param = &f.params[0].0;
    let selectors: HashSet<String> = module.fields.iter().map(|(n,_)| n.clone()).collect();
    let mut fields = HashSet::<String>::new();
    let mut deps = HashSet::<String>::new();

    fn walk(
        e: &SExpr,
        s_var: &str,
        selectors: &HashSet<String>,
        helper_names: &HashSet<String>,
        fields: &mut HashSet<String>,
        deps: &mut HashSet<String>,
    ) {
        match e {
            SExpr::Atom(_) => {}
            SExpr::List(v) if v.len()==2 => {
                if let (SExpr::Atom(h), SExpr::Atom(a)) = (&v[0], &v[1]) {
                    if selectors.contains(h) && a==s_var { fields.insert(h.clone()); return; }
                    if helper_names.contains(h) && a==s_var { deps.insert(h.clone()); return; }
                }
                for x in v { walk(x, s_var, selectors, helper_names, fields, deps); }
            }
            SExpr::List(v) => for x in v { walk(x, s_var, selectors, helper_names, fields, deps); },
        }
    }

    walk(&f.body, state_param, &selectors, helper_names, &mut fields, &mut deps);
    (fields, deps)
}

/// Compute minimized parameter lists and rewritten bodies (calls pass only required args).
fn build_parametric_helpers(
    ir: &ModelIR,
    module: &ModuleState,
) -> (
    HashMap<String, Sort>,                         // helper -> return sort
    HashMap<String, Vec<(String, Sort)>>,         // helper -> param list (field, sort) IN ORDER
    HashMap<String, Vec<String>>,                 // helper -> direct helper deps
    HashMap<String, SExpr>,                       // helper -> rewritten body
) {
    let helpers = collect_helpers(ir, module);
    let helper_names: HashSet<String> = helpers.keys().cloned().collect();

    // Direct analysis
    let mut direct_fields: HashMap<String, HashSet<String>> = HashMap::new();
    let mut direct_deps: HashMap<String, Vec<String>> = HashMap::new();
    for (name, f) in &helpers {
        let (flds, deps) = analyze_helper_direct(f, module, &helper_names);
        direct_fields.insert(name.clone(), flds);
        direct_deps.insert(name.clone(), deps.into_iter().collect());
    }

    // Topo order (deps first)
    fn topo_all(helpers: &HashSet<String>, deps: &HashMap<String, Vec<String>>) -> Vec<String> {
        fn dfs(n:&str, deps:&HashMap<String, Vec<String>>, seen:&mut HashSet<String>, out:&mut Vec<String>) {
            if !seen.insert(n.to_string()) { return; }
            if let Some(cs) = deps.get(n) { for c in cs { dfs(c, deps, seen, out); } }
            out.push(n.to_string());
        }
        let mut seen = HashSet::<String>::new();
        let mut out = Vec::<String>::new();
        for n in helpers { dfs(n, deps, &mut seen, &mut out); }
        out
    }
    let order = topo_all(&helper_names, &direct_deps);

    // Accumulate required fields transitively
    let mut req_fields: HashMap<String, HashSet<String>> = HashMap::new();
    for h in &order {
        let mut req = direct_fields.get(h).cloned().unwrap_or_default();
        if let Some(ds) = direct_deps.get(h) {
            for d in ds {
                if let Some(rfd) = req_fields.get(d) {
                    req.extend(rfd.iter().cloned());
                }
            }
        }
        req_fields.insert(h.clone(), req);
    }

    // Build per-helper param vectors (module field order for determinism)
    let field_sort_map: HashMap<String, Sort> =
        module.fields.iter().map(|(f,s)| (f.clone(), s.clone())).collect();
    let mut helper_params: HashMap<String, Vec<(String, Sort)>> = HashMap::new();
    for h in &order {
        let mut v = Vec::<(String, Sort)>::new();
        if let Some(rset) = req_fields.get(h) {
            for (fname, sort) in &module.fields {
                if rset.contains(fname) {
                    v.push((fname.clone(), sort.clone()));
                }
            }
        }
        helper_params.insert(h.clone(), v);
    }

    // Rewrite helper bodies to:
    //  - replace (|FIELD| state) -> |FIELD|
    //  - replace (G state) -> (G <params of G in its param order>)
    let mut helper_bodies = HashMap::<String, SExpr>::new();
    for (hname, f) in &helpers {
        let state_param = &f.params[0].0;
        let param_map = &helper_params; // for calls
        let selectors: HashSet<String> = field_sort_map.keys().cloned().collect();

        fn rewrite(
            e: &SExpr,
            s_var: &str,
            selectors: &HashSet<String>,
            param_map: &HashMap<String, Vec<(String, Sort)>>,
        ) -> SExpr {
            match e {
                SExpr::Atom(_) => e.clone(),
                SExpr::List(v) if v.len()==2 => {
                    if let (SExpr::Atom(h), SExpr::Atom(a)) = (&v[0], &v[1]) {
                        if selectors.contains(h) && a==s_var {
                            return atom(h.clone());
                        }
                        if let Some(params) = param_map.get(h) {
                            if a==s_var {
                                let mut call = Vec::<SExpr>::new();
                                call.push(atom(h.clone()));
                                for (fname, _) in params {
                                    call.push(atom(fname.clone()));
                                }
                                return SExpr::List(call);
                            }
                        }
                    }
                    SExpr::List(v.iter().map(|x| rewrite(x, s_var, selectors, param_map)).collect())
                }
                SExpr::List(v) => SExpr::List(v.iter().map(|x| rewrite(x, s_var, selectors, param_map)).collect()),
            }
        }

        let body = rewrite(&f.body, state_param, &selectors, &helper_params);
        helper_bodies.insert(hname.clone(), body);
    }

    // Return maps
    let helper_rets: HashMap<String, Sort> = helpers.iter().map(|(n,f)| (n.clone(), f.ret.clone())).collect();
    (helper_rets, helper_params, direct_deps, helper_bodies)
}

// ---------------- init extraction (selectors only; helpers rarely appear in _i) ----------------

fn is_true(x:&SExpr)->bool { matches!(x, SExpr::Atom(a) if a=="true") }
fn is_false(x:&SExpr)->bool{ matches!(x, SExpr::Atom(a) if a=="false") }
fn as_eq(x:&SExpr)->Option<(SExpr,SExpr)>{
    if let SExpr::List(v)=x { if v.len()==3 { if let SExpr::Atom(eq)=&v[0] { if eq=="=" { return Some((v[1].clone(),v[2].clone())); }}}}
    None
}
fn sort_is_bv1(s:&Sort)->bool{
    match &s.ast {
        SExpr::List(v) if v.len()==3 =>
            matches!(&v[0],SExpr::Atom(a) if a=="_") &&
            matches!(&v[1],SExpr::Atom(a) if a=="BitVec") &&
            matches!(&v[2],SExpr::Atom(a) if a=="1"),
        _=>false
    }
}
fn extract00_field(term:&SExpr)->Option<String>{
    if let SExpr::List(v)=term {
        if v.len()==2 {
            if let (SExpr::List(head), SExpr::Atom(arg)) = (&v[0], &v[1]) {
                if head.len()>=4 {
                    let h0 = match &head[0]{SExpr::Atom(s)=>s.as_str(), _=>""};
                    let h1 = match &head[1]{SExpr::Atom(s)=>s.as_str(), _=>""};
                    let h2 = match &head[2]{SExpr::Atom(s)=>s.as_str(), _=>""};
                    let h3 = match &head[3]{SExpr::Atom(s)=>s.as_str(), _=>""};
                    if (h0=="(_"||h0=="_") && h1=="extract" && h2=="0" && h3=="0" {
                        return Some(arg.clone());
                    }
                }
            }
        }
    }
    None
}
fn bv1_from_bool_constraint(inner_eq:&SExpr, truth:bool)->Option<(String,String)>{
    let (a,b)=as_eq(inner_eq)?;
    if let Some(fld)=extract00_field(&a) {
        if let SExpr::Atom(bit)=&b { if bit=="#b0"||bit=="#b1" {
            let want_one = bit=="#b1";
            let final_bit = if want_one==truth { "#b1" } else { "#b0" };
            return Some((fld, final_bit.to_string()));
        }}
    }
    if let Some(fld)=extract00_field(&b) {
        if let SExpr::Atom(bit)=&a { if bit=="#b0"||bit=="#b1" {
            let want_one = bit=="#b1";
            let final_bit = if want_one==truth { "#b1" } else { "#b0" };
            return Some((fld, final_bit.to_string()));
        }}
    }
    None
}
fn rewrite_init_strip_selectors(init_body:&SExpr, state_var:&str, module:&ModuleState)->SExpr{
    let selectors: HashSet<String> = module.fields.iter().map(|(n,_)| n.clone()).collect();
    fn walk(e:&SExpr, s:&str, sels:&HashSet<String>)->SExpr{
        match e {
            SExpr::Atom(_) => e.clone(),
            SExpr::List(v) if v.len()==2 => {
                if let (SExpr::Atom(h), SExpr::Atom(a)) = (&v[0], &v[1]) {
                    if sels.contains(h) && a==s { return atom(h.clone()); }
                }
                SExpr::List(v.iter().map(|x| walk(x,s,sels)).collect())
            }
            SExpr::List(v) => SExpr::List(v.iter().map(|x| walk(x,s,sels)).collect()),
        }
    }
    walk(init_body, state_var, &selectors)
}
fn extract_init_values(module:&ModuleState, init_fun:&FunDef)->HashMap<String,SExpr>{
    let state_var = &init_fun.params[0].0;
    let inlined = rewrite_init_strip_selectors(&init_fun.body, state_var, module);
    let conjuncts = flatten_and(&inlined);
    let field_sorts: HashMap<String, Sort> = module.fields.iter().map(|(f,s)|(f.clone(),s.clone())).collect();
    let mut values = HashMap::<String,SExpr>::new();
    for c in conjuncts {
        if let Some((a,b)) = as_eq(&c) {
            if let SExpr::Atom(sa)=&a { if field_sorts.contains_key(sa) { values.entry(sa.clone()).or_insert(b.clone()); continue; } }
            if let SExpr::Atom(sb)=&b { if field_sorts.contains_key(sb) { values.entry(sb.clone()).or_insert(a.clone()); continue; } }
            let (inner, truth) = if is_true(&a)||is_false(&a) { (b.clone(), is_true(&a)) }
                                 else if is_true(&b)||is_false(&b) { (a.clone(), is_true(&b)) }
                                 else { (atom(""), false) };
            if let SExpr::Atom(dummy)=&inner { if dummy.is_empty() { continue; } }
            if let Some((fld, lit)) = bv1_from_bool_constraint(&inner, truth) {
                if let Some(srt)=field_sorts.get(&fld) {
                    if sort_is_bv1(srt) { values.entry(fld).or_insert(atom(lit)); }
                }
            }
        }
    }
    values
}

// ---------------- rendering ----------------

fn render_decl_const(name: &str, sort: &Sort) -> String {
    format!("(declare-const {} {})", name, sort.to_string())
}
fn render_define_fun(name: &str, params: &[(String, Sort)], ret: &Sort, body: &SExpr) -> String {
    let mut ps = String::new();
    let mut first = true;
    for (pn, psort) in params {
        if !first { ps.push(' '); }
        first = false;
        ps.push('('); ps.push_str(pn); ps.push(' ');
        ps.push_str(&psort.to_string()); ps.push(')');
    }
    format!("(define-fun {} ({}) {} {})", name, ps, ret.to_string(), sexpr_to_string(body))
}

// ---------------- transform ----------------

pub fn transform(text: &str) -> String {
    let ir = load_model_ir(text);
    let module = ir.module.as_ref().expect("No module/state datatype found.");
    let f_t = find_transition_fun(&ir).expect("No transition function found.");
    let next_map = collect_assignments_from_t(&f_t, module);
    let state_param_name = &f_t.params[0].0;

    // Build minimized helpers
    let (helper_rets, helper_params, helper_deps, helper_bodies) = build_parametric_helpers(&ir, module);
    let helper_names: HashSet<String> = helper_rets.keys().cloned().collect();

    // Rewrite next bodies to call helpers with minimal args, collect root helpers
    fn rewrite_next_with_params(
        e: &SExpr,
        state_var: &str,
        module: &ModuleState,
        helper_params: &HashMap<String, Vec<(String, Sort)>>,
        needed: &mut HashSet<String>,
    ) -> SExpr {
        let selectors: HashSet<String> = module.fields.iter().map(|(n,_)| n.clone()).collect();
        match e {
            SExpr::Atom(_) => e.clone(),
            SExpr::List(v) if v.len()==2 => {
                if let (SExpr::Atom(h), SExpr::Atom(a)) = (&v[0], &v[1]) {
                    if selectors.contains(h) && a==state_var {
                        return atom(h.clone());
                    }
                    if let Some(params) = helper_params.get(h) {
                        if a==state_var {
                            needed.insert(h.clone());
                            let mut call = Vec::<SExpr>::new();
                            call.push(atom(h.clone()));
                            for (fname, _) in params {
                                call.push(atom(fname.clone()));
                            }
                            return SExpr::List(call);
                        }
                    }
                }
                SExpr::List(v.iter().map(|x| rewrite_next_with_params(x, state_var, module, helper_params, needed)).collect())
            }
            SExpr::List(v) => SExpr::List(v.iter().map(|x| rewrite_next_with_params(x, state_var, module, helper_params, needed)).collect()),
        }
    }

    let mut next_bodies: HashMap<String, SExpr> = HashMap::new();
    let mut root_helpers_needed = HashSet::<String>::new();
    for (field_name, _field_sort) in &module.fields {
        if let Some(lhs_expr) = next_map.get(field_name) {
            let mut needed = HashSet::<String>::new();
            let body = rewrite_next_with_params(lhs_expr, state_param_name, module, &helper_params, &mut needed);
            next_bodies.insert(field_name.clone(), body);
            root_helpers_needed.extend(needed.into_iter());
        }
    }

    // Compute reachable helpers (deps-first topo)
    fn topo_reachable(roots: &HashSet<String>, deps: &HashMap<String, Vec<String>>) -> Vec<String> {
        fn dfs(n:&str, deps:&HashMap<String, Vec<String>>, seen:&mut HashSet<String>, out:&mut Vec<String>) {
            if !seen.insert(n.to_string()) { return; }
            if let Some(cs) = deps.get(n) { for c in cs { dfs(c, deps, seen, out); } }
            out.push(n.to_string());
        }
        let mut seen = HashSet::<String>::new();
        let mut out = Vec::<String>::new();
        for r in roots { dfs(r, deps, &mut seen, &mut out); }
        out
    }
    let helper_order = topo_reachable(&root_helpers_needed, &helper_deps);

    // Init values (selectors-only)
    let init_values = if let Some(f_i) = find_init_fun(&ir) {
        extract_init_values(module, &f_i)
    } else { HashMap::new() };

    let mut out = Vec::<String>::new();
    out.push("; Flattened SMT-LIB (helpers kept, minimized params): no assertions.".into());
    out.push("; Declares base state consts, rewrites helpers to accept only used fields (transitively),".into());
    out.push("; per-field next functions call helpers with minimal args, and per-field init functions.\n".into());

    // 1) Base field consts
    out.push("; --- State field constants ---".into());
    for (fname, sort) in &module.fields {
        out.push(render_decl_const(fname, sort));
    }
    out.push("".into());

    // 2) Helper functions (only reachable)
    out.push("; --- Helper functions (minimized parameter lists) ---".into());
    for h in &helper_order {
        if let (Some(ret_sort), Some(params), Some(body)) =
            (helper_rets.get(h), helper_params.get(h), helper_bodies.get(h))
        {
            out.push(render_define_fun(h, params, ret_sort, body));
        }
    }
    out.push("".into());

    // 3) Per-field next functions
    out.push("; --- Per-field transition functions (call helpers; no inlining) ---".into());
    // We keep next_* params as ALL fields (simpler ABI). If you want, you can also minimize per-next later.
    let next_params = module.fields.clone();
    for (field_name, field_sort) in &module.fields {
        if let Some(body) = next_bodies.get(field_name) {
            let fun_name = if field_name.starts_with('|') && field_name.ends_with('|') {
                add_pipes(&format!("next {}", &field_name[1..field_name.len()-1]))
            } else { format!("next_{}", field_name) };
            out.push(render_define_fun(&fun_name, &next_params, field_sort, body));
        }
    }
    out.push("".into());

    // 4) Per-field init functions
    out.push("; --- Per-field initial value functions (only for constrained fields) ---".into());
    for (field_name, field_sort) in &module.fields {
        if let Some(body) = init_values.get(field_name) {
            let fname = if field_name.starts_with('|') && field_name.ends_with('|') {
                add_pipes(&format!("init {}", &field_name[1..field_name.len()-1]))
            } else { format!("init_{}", field_name) };
            out.push(render_define_fun(&fname, &[], field_sort, body));
        }
    }
    out.push("".into());

    out.join("\n")
}

// ---------------- main ----------------

fn main() -> io::Result<()> {
    let args: Vec<String> = env::args().collect();
    if args.len() != 3 {
        eprintln!("Usage: {} <input.smt2> <output.smt2>", args.get(0).map(String::as_str).unwrap_or("smt_flatten"));
        std::process::exit(2);
    }
    let text = fs::read_to_string(&args[1])?;
    let out = transform(&text);
    fs::write(&args[2], out)?;
    println!("Wrote {}", &args[2]);
    Ok(())
}
