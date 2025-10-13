use indexmap::IndexMap;
use z3::{ast::{Ast, Bool, Dynamic, Int, BV}, Context};

use std::str::FromStr;

// Bring your IR into scope:
use ir::{SMVEnv, VarType, ReturnType}; // adjust path: crate::ir::<...>
use macros::*; // bool_var!, int_var!, bv_var!

// ---------------------------
// Simple S-expression parser
// ---------------------------

#[derive(Clone, Debug)]
enum SExp {
    Atom(String),
    List(Vec<SExp>),
}

fn strip_pipes(s: &str) -> String {
    let s = s.trim();
    if s.starts_with('|') && s.ends_with('|') && s.len() >= 2 {
        s[1..s.len()-1].to_string()
    } else {
        s.to_string()
    }
}

fn tokenize(mut s: &str) -> Vec<String> {
    // Remove line comments starting with ';'
    let mut cleaned = String::with_capacity(s.len());
    for line in s.lines() {
        if let Some(idx) = line.find(';') {
            cleaned.push_str(&line[..idx]);
            cleaned.push('\n');
        } else {
            cleaned.push_str(line);
            cleaned.push('\n');
        }
    }
    s = &cleaned;

    // Tokenize parentheses, atoms, and pipe-delimited symbols verbatim
    let mut toks = Vec::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        match chars[i] {
            c if c.is_whitespace() => { i += 1; }
            '(' | ')' => {
                toks.push(chars[i].to_string());
                i += 1;
            }
            '|' => {
                // read until next '|'
                let start = i;
                i += 1;
                while i < chars.len() && chars[i] != '|' { i += 1; }
                if i < chars.len() && chars[i] == '|' { i += 1; }
                toks.push(chars[start..i].iter().collect());
            }
            _ => {
                let start = i;
                while i < chars.len() && !chars[i].is_whitespace() && chars[i] != '(' && chars[i] != ')' {
                    i += 1;
                }
                toks.push(chars[start..i].iter().collect());
            }
        }
    }
    toks
}

fn parse_list(tokens: &[String], pos: &mut usize) -> Result<SExp, String> {
    let mut out = Vec::new();
    while *pos < tokens.len() {
        match tokens[*pos].as_str() {
            "(" => {
                *pos += 1;
                out.push(parse_list(tokens, pos)?);
            }
            ")" => {
                *pos += 1;
                return Ok(SExp::List(out));
            }
            tok => {
                if tok == ")" { break; }
                out.push(SExp::Atom(tok.to_string()));
                *pos += 1;
            }
        }
    }
    Err("Unbalanced parentheses".into())
}

fn parse_sexps(s: &str) -> Result<Vec<SExp>, String> {
    let toks = tokenize(s);
    let mut pos = 0;
    let mut items = Vec::new();
    while pos < toks.len() {
        match toks[pos].as_str() {
            "(" => {
                pos += 1;
                items.push(parse_list(&toks, &mut pos)?);
            }
            ")" => return Err("Unexpected ')'".into()),
            _ => {
                // standalone atom (rare in SMT-LIB top-level)
                items.push(SExp::Atom(toks[pos].clone()));
                pos += 1;
            }
        }
    }
    Ok(items)
}

// ---------------------------
// Lightweight AST for bodies
// ---------------------------

#[derive(Clone, Debug)]
enum Sort {
    Bool,
    Int,
    BV(u32),
}

#[derive(Clone, Debug)]
enum Expr {
    Sym(String),                // variable reference
    BoolConst(bool),
    BVConst { bits: String },   // "#b0101" (we derive width from len)
    IntConst(i64),

    Eq(Box<Expr>, Box<Expr>),
    Ite(Box<Expr>, Box<Expr>, Box<Expr>),
    Extract { hi: u32, lo: u32, e: Box<Expr> },
}

// ---------------------------
// Parse helpers
// ---------------------------

fn parse_sort(sexp: &SExp) -> Result<Sort, String> {
    match sexp {
        SExp::Atom(a) if a == "Bool" => Ok(Sort::Bool),
        SExp::Atom(a) if a == "Int"  => Ok(Sort::Int),
        SExp::List(items) => {
            // (_ BitVec n)
            if items.len() == 3 {
                if let (SExp::Atom(ul), SExp::Atom(bv), SExp::Atom(n)) = (&items[0], &items[1], &items[2]) {
                    if ul == "_" && bv == "BitVec" {
                        let w: u32 = n.parse().map_err(|_| "Bad BitVec width".to_string())?;
                        return Ok(Sort::BV(w));
                    }
                }
            }
            Err(format!("Unsupported sort: {:?}", sexp))
        }
        _ => Err(format!("Unsupported sort: {:?}", sexp)),
    }
}

fn parse_expr(sexp: &SExp) -> Result<Expr, String> {
    match sexp {
        SExp::Atom(a) => {
            if a == "true" { return Ok(Expr::BoolConst(true)); }
            if a == "false" { return Ok(Expr::BoolConst(false)); }
            if a.starts_with("#b") { return Ok(Expr::BVConst { bits: a[2..].to_string() }); }
            // integer? (rare in your flattened BVs, but harmless)
            if let Ok(v) = i64::from_str(a) { return Ok(Expr::IntConst(v)); }
            Ok(Expr::Sym(strip_pipes(a)))
        }
        SExp::List(v) if v.is_empty() => Err("Empty list".into()),
        SExp::List(v) => {
            // special forms: (= a b) (ite c t e) (( _ extract i j ) x)
            if let SExp::Atom(op) = &v[0] {
                match op.as_str() {
                    "=" => {
                        if v.len() != 3 { return Err("= expects 2 args".into()); }
                        Ok(Expr::Eq(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                    }
                    "ite" => {
                        if v.len() != 4 { return Err("ite expects 3 args".into()); }
                        Ok(Expr::Ite(
                            Box::new(parse_expr(&v[1])?),
                            Box::new(parse_expr(&v[2])?),
                            Box::new(parse_expr(&v[3])?),
                        ))
                    }
                    "_" => {
                        // shouldn't appear like this at top; extract is usually nested as ((_ extract hi lo) E)
                        Err("Bare '_'".into())
                    }
                    _ => {
                        // Might be ((_ extract i j) e)
                        if let SExp::List(head) = &v[0] {
                            if head.len() == 4 {
                                if let (SExp::Atom(ul), SExp::Atom(ex), SExp::Atom(hi), SExp::Atom(lo)) =
                                    (&head[0], &head[1], &head[2], &head[3]) {
                                    if ul == "_" && ex == "extract" && v.len() == 2 {
                                        let hi: u32 = hi.parse().map_err(|_| "bad extract hi".to_string())?;
                                        let lo: u32 = lo.parse().map_err(|_| "bad extract lo".to_string())?;
                                        return Ok(Expr::Extract { hi, lo, e: Box::new(parse_expr(&v[1])?) });
                                    }
                                }
                            }
                        }
                        // Fallback: treat as symbol application -> but our subset doesn't need it
                        Err(format!("Unsupported form: {:?}", v))
                    }
                }
            } else {
                Err("Bad list head".into())
            }
        }
    }
}

// ---------------------------
// Convert Expr -> Z3 Dynamic
// ---------------------------

struct TyCtxt {
    // variable -> Sort
    vars: IndexMap<String, Sort>,
}

fn bv_from_bits<'ctx>(ctx: &'ctx Context, bits: &str) -> BV<'ctx> {
    let width = bits.len() as u32;
    // parse as unsigned
    let mut val: i64 = 0;
    for c in bits.chars() {
        val = (val << 1) | if c == '1' { 1 } else { 0 };
    }
    BV::from_i64(ctx, val, width)
}

fn expr_to_ast<'ctx>(
    e: &Expr,
    ctx: &'ctx Context,
    st: &IndexMap<&'ctx str, Dynamic<'ctx>>,
    tys: &TyCtxt,
) -> Result<Dynamic<'ctx>, String> {
    match e {
        Expr::Sym(s) => {
            let key = leak_str(s);
            st.get(key)
                .cloned()
                .ok_or_else(|| format!("Unknown symbol in body: {}", s))
        }
        Expr::BoolConst(b) => Ok(Bool::from_bool(ctx, *b).into()),
        Expr::IntConst(i)   => Ok(Int::from_i64(ctx, *i).into()),
        Expr::BVConst { bits } => Ok(bv_from_bits(ctx, bits).into()),

        Expr::Eq(a, b) => {
            let da = expr_to_ast(a, ctx, st, tys)?;
            let db = expr_to_ast(b, ctx, st, tys)?;
            let out = if let (Some(x), Some(y)) = (da.as_bool(), db.as_bool()) {
                x._eq(&y).into()
            } else if let (Some(x), Some(y)) = (da.as_int(), db.as_int()) {
                x._eq(&y).into()
            } else if let (Some(x), Some(y)) = (da.as_bv(), db.as_bv()) {
                x._eq(&y).into()
            } else {
                return Err("Type mismatch in '='".into());
            };
            Ok(out)
        }

        Expr::Ite(c, t, e2) => {
            let dc = expr_to_ast(c, ctx, st, tys)?.as_bool().ok_or("ITE cond not Bool")?;
            let dt = expr_to_ast(t, ctx, st, tys)?;
            let de = expr_to_ast(e2, ctx, st, tys)?;
            if let (Some(tt), Some(ee)) = (dt.as_bool(), de.as_bool()) {
                Ok(Bool::ite(&dc, &tt, &ee).into())
            } else if let (Some(tt), Some(ee)) = (dt.as_int(), de.as_int()) {
                Ok(tt.ite(&dc, &ee).into()) // Int has ite via Ast (Z3 sorts agree)
            } else if let (Some(tt), Some(ee)) = (dt.as_bv(), de.as_bv()) {
                Ok(tt.ite(&dc, &ee).into())
            } else {
                Err("ITE branches have different types".into())
            }
        }

        Expr::Extract { hi, lo, e } => {
            let de = expr_to_ast(e, ctx, st, tys)?;
            let bv = de.as_bv().ok_or("extract on non-BV")?;
            Ok(bv.extract(*hi, *lo).into())
        }
    }
}

// ---------------------------
// Top-level driver
// ---------------------------

#[derive(Default)]
struct Decl {
    name: String,
    sort: Sort,
}

#[derive(Default)]
struct NextDef {
    var: String,
    ret_sort: Sort,
    body: Expr,
}

#[derive(Default)]
struct InitDef {
    var: String,
    ret_sort: Sort,
    body: Expr,
}

fn is_atom(s: &SExp, expect: &str) -> bool {
    matches!(s, SExp::Atom(a) if a == expect)
}

fn leak_str(s: &str) -> &'static str {
    Box::leak(s.to_string().into_boxed_str())
}

pub fn build_env_from_flat_smt<'ctx>(ctx: &'ctx Context, smt: &str) -> Result<SMVEnv<'ctx>, String> {
    let sexps = parse_sexps(smt)?;

    let mut decls: Vec<Decl> = Vec::new();
    let mut nexts: Vec<NextDef> = Vec::new();
    let mut inits: Vec<InitDef> = Vec::new();

    // 1) Collect DECLAREs and DEFINEs
    for top in sexps {
        match &top {
            SExp::List(items) if !items.is_empty() => {
                if let SExp::Atom(head) = &items[0] {
                    match head.as_str() {
                        "declare-const" => {
                            // (declare-const |x| Sort)
                            if items.len() != 3 { return Err("declare-const arity".into()); }
                            let name = match &items[1] { SExp::Atom(a) => strip_pipes(a), _ => return Err("declare-const name".into()) };
                            let sort = parse_sort(&items[2])?;
                            decls.push(Decl { name, sort });
                        }
                        "define-fun" => {
                            // (define-fun |name| ( (|arg| Sort) ... ) RetSort Body )
                            if items.len() != 5 { return Err("define-fun arity".into()); }
                            let raw_name = match &items[1] { SExp::Atom(a) => strip_pipes(a), _ => return Err("define-fun name".into()) };
                            let _params = &items[2]; // we don't need them; we read from state
                            let ret_sort = parse_sort(&items[3])?;
                            let body = parse_expr(&items[4])?;

                            if let Some(rest) = raw_name.strip_prefix("next ") {
                                nexts.push(NextDef { var: rest.to_string(), ret_sort, body });
                            } else if let Some(rest) = raw_name.strip_prefix("init ") {
                                inits.push(InitDef { var: rest.to_string(), ret_sort, body });
                            } else {
                                // ignore other helpers if any
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    // 2) Build type context from DECLAREs
    let mut tys = TyCtxt { vars: IndexMap::new() };
    for d in &decls {
        tys.vars.insert(d.name.clone(), d.sort.clone());
    }

    // 3) Create env + register variables
    let mut env = SMVEnv::new(ctx);
    for d in &decls {
        let name_ref: &'static str = leak_str(&d.name);
        match &d.sort {
            Sort::Bool => env.register_variable(name_ref, VarType::Bool { init: None }),
            Sort::Int  => env.register_variable(name_ref, VarType::Int  { init: None, lower: None, upper: None }),
            Sort::BV(w) => env.register_variable(name_ref, VarType::BVector { width: *w, lower: None, upper: None, init: None }),
        }
    }

    // 4) Fill initials from INIT define-funs
    for init in &inits {
        let name_ref: &'static str = leak_str(&init.var);
        let var_t = env.get_variable_type(name_ref)
            .ok_or_else(|| format!("init for undeclared var {}", init.var))?
            .clone();

        match (var_t, &init.ret_sort) {
            (VarType::Bool{..}, Sort::Bool) => {
                let val = match &init.body {
                    Expr::BoolConst(b) => *b,
                    Expr::Eq(_,_) | Expr::Ite(_,_,_) | Expr::Extract{..} | Expr::Sym(_) => {
                        return Err(format!("init {} expected constant Bool", init.var))
                    }
                    Expr::BVConst{..} | Expr::IntConst(_) => {
                        return Err(format!("init {} sort mismatch Bool vs const", init.var))
                    }
                };
                if let Some(v) = env.get_variable_mut(name_ref) {
                    *v = crate::ir::Variable { sort: VarType::Bool { init: Some(vec![val]) } };
                }
            }
            (VarType::BVector{width, ..}, Sort::BV(_w)) => {
                let bits = if let Expr::BVConst{bits} = &init.body {
                    bits.clone()
                } else {
                    return Err(format!("init {} expected BV const", init.var));
                };
                let val_bv = bv_from_bits(ctx, &bits);
                let as_i = val_bv.as_u64().unwrap_or(0) as i64;
                if let Some(v) = env.get_variable_mut(name_ref) {
                    *v = crate::ir::Variable {
                        sort: VarType::BVector { width, lower: None, upper: None, init: Some(vec![as_i]) }
                    };
                }
            }
            (VarType::Int{..}, Sort::Int) => {
                let ival = if let Expr::IntConst(i) = init.body { i } else {
                    return Err(format!("init {} expected Int const", init.var));
                };
                if let Some(v) = env.get_variable_mut(name_ref) {
                    *v = crate::ir::Variable { sort: VarType::Int { init: Some(vec![ival]), lower: None, upper: None } };
                }
            }
            _ => {
                return Err(format!("init {} sort mismatch", init.var));
            }
        }
    }

    // 5) Register transitions from NEXT define-funs
    //    We compile each body to a closure that, given a current state, rebuilds the RHS AST.
    for nxt in &nexts {
        let var_name: &'static str = leak_str(&nxt.var);
        let body_ir = nxt.body.clone();
        let tys_ir = tys.clone();

        env.register_transition(
            var_name,
            // cond ≡ true
            |_env, ctx, _st| ReturnType::Bool(vec![true]),
            move |_env, ctx, st| {
                let dyn_ast = expr_to_ast(&body_ir, ctx, st, &tys_ir)
                    .expect("Failed to translate next-body into Z3 AST");
                ReturnType::DynAst(dyn_ast)
            }
        );
    }

    Ok(env)
}
