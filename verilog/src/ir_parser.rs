use indexmap::IndexMap;
use z3::{ast::{Ast, Bool, Dynamic, Int, BV}, Context};

type InlineKey = (String, Vec<u64>);
type InlineMemo = IndexMap<InlineKey, Expr>;

// === Bring your IR into scope (adjust paths) ===
use ir::{SMVEnv, VarType, ReturnType, Variable};

// ---------------------------
// S-expression + Mini-IR
// ---------------------------

#[derive(Clone, Debug)]
enum SExp { Atom(String), List(Vec<SExp>) }

#[derive(Clone, Debug)]
enum Sort { Bool, Int, BV(u32) }

#[derive(Clone, Debug)]
enum Expr {
    Sym(String),
    BoolConst(bool),
    IntConst(i64),
    BVConst { bits: String },
    Eq(Box<Expr>, Box<Expr>),
    Ite(Box<Expr>, Box<Expr>, Box<Expr>),
    Extract { hi: u32, lo: u32, e: Box<Expr> },

    And(Vec<Expr>),
    Or(Vec<Expr>),
    Not(Box<Expr>),

    Xor(Vec<Expr>),         // Bool XOR (already present)
    BVXor(Vec<Expr>),       // BV XOR (already present)

    // === New: BV algebra / logic ===
    BVAnd(Vec<Expr>),
    BVOr(Vec<Expr>),
    BVNot(Box<Expr>),
    BVNeg(Box<Expr>),

    BVAdd(Vec<Expr>),
    BVSub(Box<Expr>, Box<Expr>),
    BVMul(Vec<Expr>),

    BVUDiv(Box<Expr>, Box<Expr>),
    BVURem(Box<Expr>, Box<Expr>),
    BVSDiv(Box<Expr>, Box<Expr>),
    BVSRem(Box<Expr>, Box<Expr>),
    BVSMod(Box<Expr>, Box<Expr>),

    BVShl (Box<Expr>, Box<Expr>),
    BVLshr(Box<Expr>, Box<Expr>),
    BVAshr(Box<Expr>, Box<Expr>),

    Concat(Vec<Expr>),
    ZeroExtend { k: u32, e: Box<Expr> },
    SignExtend { k: u32, e: Box<Expr> },

    // BV comparisons (Bool results)
    BVUlt(Box<Expr>, Box<Expr>),
    BVUle(Box<Expr>, Box<Expr>),
    BVUgt(Box<Expr>, Box<Expr>),
    BVUge(Box<Expr>, Box<Expr>),
    BVSlt(Box<Expr>, Box<Expr>),
    BVSle(Box<Expr>, Box<Expr>),
    BVSgt(Box<Expr>, Box<Expr>),
    BVSge(Box<Expr>, Box<Expr>),

    Distinct(Vec<Expr>),
    App(String, Vec<Expr>),
}


#[derive(Clone, Debug)]
struct FnDef {
    params: Vec<(String, Sort)>,
    ret: Sort,
    body: Expr,
}

// ---------------------------
// Tokenize / Parse SExp
// ---------------------------

fn strip_pipes(s: &str) -> String {
    let s = s.trim();
    if s.starts_with('|') && s.ends_with('|') && s.len() >= 2 { s[1..s.len()-1].to_string() }
    else { s.to_string() }
}

fn tokenize(source: &str) -> Vec<String> {
    // strip ; comments
    let mut cleaned = String::with_capacity(source.len());
    for line in source.lines() {
        if let Some(i) = line.find(';') { cleaned.push_str(&line[..i]); cleaned.push('\n'); }
        else { cleaned.push_str(line); cleaned.push('\n'); }
    }
    let s = cleaned;

    let mut toks = Vec::new();
    let ch: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < ch.len() {
        match ch[i] {
            c if c.is_whitespace() => i += 1,
            '(' | ')' => { toks.push(ch[i].to_string()); i += 1; }
            '|' => {
                let start = i; i += 1;
                while i < ch.len() && ch[i] != '|' { i += 1; }
                if i < ch.len() { i += 1; }
                toks.push(ch[start..i].iter().collect());
            }
            _ => {
                let start = i;
                while i < ch.len() && !ch[i].is_whitespace() && ch[i] != '(' && ch[i] != ')' { i += 1; }
                toks.push(ch[start..i].iter().collect());
            }
        }
    }
    toks
}

fn parse_list(tokens: &[String], pos: &mut usize) -> Result<SExp, String> {
    let mut out = Vec::new();
    while *pos < tokens.len() {
        match tokens[*pos].as_str() {
            "(" => { *pos += 1; out.push(parse_list(tokens, pos)?); }
            ")" => { *pos += 1; return Ok(SExp::List(out)); }
            tok => { out.push(SExp::Atom(tok.to_string())); *pos += 1; }
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
            "(" => { pos += 1; items.push(parse_list(&toks, &mut pos)?); }
            ")" => return Err("Unexpected ')'".into()),
            _   => { items.push(SExp::Atom(toks[pos].clone())); pos += 1; }
        }
    }
    Ok(items)
}

// ---------------------------
// SMT sorts / Expr parser
// ---------------------------

fn parse_sort(s: &SExp) -> Result<Sort, String> {
    match s {
        SExp::Atom(a) if a == "Bool" => Ok(Sort::Bool),
        SExp::Atom(a) if a == "Int"  => Ok(Sort::Int),
        SExp::List(v) if v.len() == 3 => {
            if let (SExp::Atom(u), SExp::Atom(bv), SExp::Atom(n)) = (&v[0], &v[1], &v[2]) {
                if u == "_" && bv == "BitVec" {
                    let w: u32 = n.parse().map_err(|_| "Bad BitVec width".to_string())?;
                    return Ok(Sort::BV(w));
                }
            }
            Err(format!("Unsupported sort: {:?}", s))
        }
        _ => Err(format!("Unsupported sort: {:?}", s)),
    }
}

fn parse_expr(e: &SExp) -> Result<Expr, String> {
    match e {
        SExp::Atom(a) => {
            if a == "true"  { return Ok(Expr::BoolConst(true)); }
            if a == "false" { return Ok(Expr::BoolConst(false)); }
            if a.starts_with("#b") { return Ok(Expr::BVConst { bits: a[2..].to_string() }); }
            if let Ok(i) = a.parse::<i64>() { return Ok(Expr::IntConst(i)); }
            return Ok(Expr::Sym(strip_pipes(a)));
        }
        SExp::List(v) if v.is_empty() => Err("Empty list".into()),
        SExp::List(v) => {
            // ((_ extract hi lo) e)
            if let SExp::List(head) = &v[0] {
                if head.len() == 4 {
                    if let (SExp::Atom(u), SExp::Atom(ex), SExp::Atom(hi), SExp::Atom(lo)) =
                        (&head[0], &head[1], &head[2], &head[3]) {
                        if u == "_" && ex == "extract" && v.len() == 2 {
                            let hi: u32 = hi.parse().map_err(|_| "bad extract hi".to_string())?;
                            let lo: u32 = lo.parse().map_err(|_| "bad extract lo".to_string())?;
                            return Ok(Expr::Extract { hi, lo, e: Box::new(parse_expr(&v[1])?) });
                        }
                    }
                }
                if head.len() == 3 {
                    if let (SExp::Atom(u), SExp::Atom(op), SExp::Atom(k)) = (&head[0], &head[1], &head[2]) {
                        if u == "_" && op == "zero_extend" && v.len() == 2 {
                            let k: u32 = k.parse().map_err(|_| "bad zero_extend k".to_string())?;
                            return Ok(Expr::ZeroExtend { k, e: Box::new(parse_expr(&v[1])?) });
                        }
                        if u == "_" && op == "sign_extend" && v.len() == 2 {
                            let k: u32 = k.parse().map_err(|_| "bad sign_extend k".to_string())?;
                            return Ok(Expr::SignExtend { k, e: Box::new(parse_expr(&v[1])?) });
                        }
                    }
                }
            }

            // head is an atom (operator / symbol)
            let head = match &v[0] { SExp::Atom(a) => a.as_str(), _ => return Err("Bad head".into()) };
            match head {
                "=" => {
                    if v.len() != 3 { return Err("= expects 2 args".into()); }
                    Ok(Expr::Eq(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "ite" => {
                    if v.len() != 4 { return Err("ite expects 3 args".into()); }
                    Ok(Expr::Ite(
                        Box::new(parse_expr(&v[1])?),
                        Box::new(parse_expr(&v[2])?),
                        Box::new(parse_expr(&v[3])?)
                    ))
                }
                "and" => {
                    let mut xs = Vec::new();
                    for a in &v[1..] { xs.push(parse_expr(a)?); }
                    Ok(Expr::And(xs))
                }
                "or" => {
                    let mut xs = Vec::new();
                    for a in &v[1..] { xs.push(parse_expr(a)?); }
                    Ok(Expr::Or(xs))
                }
                "not" => {
                    if v.len() != 2 { return Err("not expects 1 arg".into()); }
                    Ok(Expr::Not(Box::new(parse_expr(&v[1])?)))
                }
                "xor" => {
                    // Boolean XOR: accept 1+ args (xor a) == a; (xor a b c) == a ^ b ^ c
                    let mut xs = Vec::with_capacity(v.len().saturating_sub(1));
                    for a in &v[1..] { xs.push(parse_expr(a)?); }
                    Ok(Expr::Xor(xs))
                }
                "bvxor" => {
                    // Bitvector XOR: 2+ args
                    let mut xs = Vec::with_capacity(v.len().saturating_sub(1));
                    for a in &v[1..] { xs.push(parse_expr(a)?); }
                    Ok(Expr::BVXor(xs))
                }
                "bvand" => {
                    let mut xs = Vec::new(); for a in &v[1..] { xs.push(parse_expr(a)?); }
                    if xs.len() < 2 { return Err("bvand expects >=2 args".into()); }
                    Ok(Expr::BVAnd(xs))
                }
                "bvor" => {
                    let mut xs = Vec::new(); for a in &v[1..] { xs.push(parse_expr(a)?); }
                    if xs.len() < 2 { return Err("bvor expects >=2 args".into()); }
                    Ok(Expr::BVOr(xs))
                }
                "bvnot" => {
                    if v.len() != 2 { return Err("bvnot expects 1 arg".into()); }
                    Ok(Expr::BVNot(Box::new(parse_expr(&v[1])?)))
                }
                "bvneg" => {
                    if v.len() != 2 { return Err("bvneg expects 1 arg".into()); }
                    Ok(Expr::BVNeg(Box::new(parse_expr(&v[1])?)))
                }
                "bvadd" => {
                    let mut xs = Vec::new(); for a in &v[1..] { xs.push(parse_expr(a)?); }
                    if xs.len() < 2 { return Err("bvadd expects >=2 args".into()); }
                    Ok(Expr::BVAdd(xs))
                }
                "bvsub" => {
                    if v.len() != 3 { return Err("bvsub expects 2 args".into()); }
                    Ok(Expr::BVSub(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvmul" => {
                    let mut xs = Vec::new(); for a in &v[1..] { xs.push(parse_expr(a)?); }
                    if xs.len() < 2 { return Err("bvmul expects >=2 args".into()); }
                    Ok(Expr::BVMul(xs))
                }
                "bvudiv" => {
                    if v.len() != 3 { return Err("bvudiv expects 2 args".into()); }
                    Ok(Expr::BVUDiv(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvurem" => {
                    if v.len() != 3 { return Err("bvurem expects 2 args".into()); }
                    Ok(Expr::BVURem(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvsdiv" => {
                    if v.len() != 3 { return Err("bvsdiv expects 2 args".into()); }
                    Ok(Expr::BVSDiv(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvsrem" => {
                    if v.len() != 3 { return Err("bvsrem expects 2 args".into()); }
                    Ok(Expr::BVSRem(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvsmod" => {
                    if v.len() != 3 { return Err("bvsmod expects 2 args".into()); }
                    Ok(Expr::BVSMod(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvshl" => {
                    if v.len() != 3 { return Err("bvshl expects 2 args".into()); }
                    Ok(Expr::BVShl(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvlshr" => {
                    if v.len() != 3 { return Err("bvlshr expects 2 args".into()); }
                    Ok(Expr::BVLshr(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvashr" => {
                    if v.len() != 3 { return Err("bvashr expects 2 args".into()); }
                    Ok(Expr::BVAshr(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "concat" => {
                    let mut xs = Vec::new(); for a in &v[1..] { xs.push(parse_expr(a)?); }
                    if xs.len() < 2 { return Err("concat expects >=2 args".into()); }
                    Ok(Expr::Concat(xs))
                }
                "bvult" => { if v.len()!=3 {return Err("bvult expects 2 args".into());}
                    Ok(Expr::BVUlt(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvule" => { if v.len()!=3 {return Err("bvule expects 2 args".into());}
                    Ok(Expr::BVUle(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvugt" => { if v.len()!=3 {return Err("bvugt expects 2 args".into());}
                    Ok(Expr::BVUgt(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvuge" => { if v.len()!=3 {return Err("bvuge expects 2 args".into());}
                    Ok(Expr::BVUge(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvslt" => { if v.len()!=3 {return Err("bvslt expects 2 args".into());}
                    Ok(Expr::BVSlt(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvsle" => { if v.len()!=3 {return Err("bvsle expects 2 args".into());}
                    Ok(Expr::BVSle(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvsgt" => { if v.len()!=3 {return Err("bvsgt expects 2 args".into());}
                    Ok(Expr::BVSgt(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "bvsge" => { if v.len()!=3 {return Err("bvsge expects 2 args".into());}
                    Ok(Expr::BVSge(Box::new(parse_expr(&v[1])?), Box::new(parse_expr(&v[2])?)))
                }
                "distinct" => {
                    // SMT-LIB allows 0+ args; we accept any arity here.
                    let mut xs = Vec::with_capacity(v.len().saturating_sub(1));
                    for a in &v[1..] { xs.push(parse_expr(a)?); }
                    Ok(Expr::Distinct(xs))
                }

                // Otherwise: helper application
                _ => {
                    let name = strip_pipes(&v[0].as_atom().unwrap_or_default());
                    let mut args = Vec::new();
                    for a in &v[1..] { args.push(parse_expr(a)?); }
                    Ok(Expr::App(name, args))
                }
            }
        }
    }
}

trait AsAtom {
    fn as_atom(&self) -> Option<String>;
}
impl AsAtom for SExp {
    fn as_atom(&self) -> Option<String> {
        if let SExp::Atom(a) = self { Some(a.clone()) } else { None }
    }
}

// ---------------------------
// Helpers: inline-on-demand
// ---------------------------

type FnTable = IndexMap<String, FnDef>;

fn subst_expr(e: &Expr, sub: &IndexMap<String, Expr>) -> Expr {
    match e {
        Expr::Sym(s) => sub.get(s).cloned().unwrap_or_else(|| Expr::Sym(s.clone())),
        Expr::BoolConst(_) | Expr::IntConst(_) | Expr::BVConst{..} => e.clone(),
        Expr::Eq(a,b) => Expr::Eq(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::Ite(c,t,ee) => Expr::Ite(
            Box::new(subst_expr(c, sub)),
            Box::new(subst_expr(t, sub)),
            Box::new(subst_expr(ee, sub))
        ),
        Expr::Extract{hi,lo,e:ee} => Expr::Extract{ hi:*hi, lo:*lo, e:Box::new(subst_expr(ee, sub)) },
        Expr::And(xs)   => Expr::And(xs.iter().map(|x| subst_expr(x, sub)).collect()),
        Expr::Or(xs)    => Expr::Or(xs.iter().map(|x| subst_expr(x, sub)).collect()),
        Expr::Not(x)    => Expr::Not(Box::new(subst_expr(x, sub))),
        Expr::Xor(xs)   => Expr::Xor(xs.iter().map(|x| subst_expr(x, sub)).collect()),
        Expr::BVXor(xs) => Expr::BVXor(xs.iter().map(|x| subst_expr(x, sub)).collect()),
        Expr::Xor(xs)     => Expr::Xor(xs.iter().map(|x| subst_expr(x, sub)).collect()),
        Expr::BVXor(xs)   => Expr::BVXor(xs.iter().map(|x| subst_expr(x, sub)).collect()),

        Expr::BVAnd(xs)   => Expr::BVAnd(xs.iter().map(|x| subst_expr(x, sub)).collect()),
        Expr::BVOr(xs)    => Expr::BVOr(xs.iter().map(|x| subst_expr(x, sub)).collect()),
        Expr::BVNot(x)    => Expr::BVNot(Box::new(subst_expr(x, sub))),
        Expr::BVNeg(x)    => Expr::BVNeg(Box::new(subst_expr(x, sub))),

        Expr::BVAdd(xs)   => Expr::BVAdd(xs.iter().map(|x| subst_expr(x, sub)).collect()),
        Expr::BVSub(a,b)  => Expr::BVSub(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVMul(xs)   => Expr::BVMul(xs.iter().map(|x| subst_expr(x, sub)).collect()),

        Expr::BVUDiv(a,b) => Expr::BVUDiv(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVURem(a,b) => Expr::BVURem(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVSDiv(a,b) => Expr::BVSDiv(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVSRem(a,b) => Expr::BVSRem(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVSMod(a,b) => Expr::BVSMod(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),

        Expr::BVShl(a,b)  => Expr::BVShl (Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVLshr(a,b) => Expr::BVLshr(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVAshr(a,b) => Expr::BVAshr(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),

        Expr::Concat(xs)  => Expr::Concat(xs.iter().map(|x| subst_expr(x, sub)).collect()),
        Expr::ZeroExtend{k,e} => Expr::ZeroExtend{ k:*k, e:Box::new(subst_expr(e, sub)) },
        Expr::SignExtend{k,e} => Expr::SignExtend{ k:*k, e:Box::new(subst_expr(e, sub)) },

        Expr::BVUlt(a,b)  => Expr::BVUlt(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVUle(a,b)  => Expr::BVUle(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVUgt(a,b)  => Expr::BVUgt(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVUge(a,b)  => Expr::BVUge(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVSlt(a,b)  => Expr::BVSlt(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVSle(a,b)  => Expr::BVSle(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVSgt(a,b)  => Expr::BVSgt(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::BVSge(a,b)  => Expr::BVSge(Box::new(subst_expr(a, sub)), Box::new(subst_expr(b, sub))),
        Expr::Distinct(xs) => Expr::Distinct(xs.iter().map(|x| subst_expr(x, sub)).collect()),

        Expr::App(n, args) => Expr::App(n.clone(), args.iter().map(|x| subst_expr(x, sub)).collect()),
    }
}


fn inline_helpers(e: &Expr, fns: &FnTable, depth: usize) -> Result<Expr, String> {
    if depth > 256 { return Err("helper expansion depth exceeded".into()); }
    match e {
        Expr::App(name, args) if fns.contains_key(name) => {
            let def = &fns[name];
            if def.params.len() != args.len() {
                return Err(format!("arity mismatch in call {}: expected {}, got {}", name, def.params.len(), args.len()));
            }
            // first inline args
            let mut inlined_args = Vec::new();
            for a in args { inlined_args.push(inline_helpers(a, fns, depth+1)?); }
            // build substitution map
            let mut sub = IndexMap::new();
            for ((p, _psort), act) in def.params.iter().zip(inlined_args.into_iter()) {
                sub.insert(p.clone(), act);
            }
            // substitute into body, then continue inlining recursively
            let body_sub = subst_expr(&def.body, &sub);
            inline_helpers(&body_sub, fns, depth+1)
        }
        // Recurse
        Expr::Eq(a,b) => Ok(Expr::Eq(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::Ite(c,t,ee) => Ok(Expr::Ite(
            Box::new(inline_helpers(c,fns,depth+1)?),
            Box::new(inline_helpers(t,fns,depth+1)?),
            Box::new(inline_helpers(ee,fns,depth+1)?),
        )),
        Expr::Extract{hi,lo,e:ee} => Ok(Expr::Extract{hi:*hi,lo:*lo,e:Box::new(inline_helpers(ee,fns,depth+1)?) }),
        Expr::And(xs) => Ok(Expr::And(xs.iter().map(|x| inline_helpers(x,fns,depth+1)).collect::<Result<Vec<_>,_>>()?)),
        Expr::Or(xs)  => Ok(Expr::Or(xs.iter().map(|x| inline_helpers(x,fns,depth+1)).collect::<Result<Vec<_>,_>>()?)),
        Expr::Not(x)  => Ok(Expr::Not(Box::new(inline_helpers(x,fns,depth+1)?))),
        Expr::Xor(xs)   => Ok(Expr::Xor(xs.iter().map(|x| inline_helpers(x,fns,depth+1)).collect::<Result<Vec<_>,_>>()?)),
        Expr::BVXor(xs) => Ok(Expr::BVXor(xs.iter().map(|x| inline_helpers(x,fns,depth+1)).collect::<Result<Vec<_>,_>>()?)),

        Expr::BVAnd(xs) => Ok(Expr::BVAnd(xs.iter().map(|x| inline_helpers(x,fns,depth+1)).collect::<Result<Vec<_>,_>>()?)),
        Expr::BVOr(xs)  => Ok(Expr::BVOr(xs.iter().map(|x| inline_helpers(x,fns,depth+1)).collect::<Result<Vec<_>,_>>()?)),
        Expr::BVNot(x)  => Ok(Expr::BVNot(Box::new(inline_helpers(x,fns,depth+1)?))),
        Expr::BVNeg(x)  => Ok(Expr::BVNeg(Box::new(inline_helpers(x,fns,depth+1)?))),

        Expr::BVAdd(xs) => Ok(Expr::BVAdd(xs.iter().map(|x| inline_helpers(x,fns,depth+1)).collect::<Result<Vec<_>,_>>()?)),
        Expr::BVSub(a,b)=> Ok(Expr::BVSub(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVMul(xs) => Ok(Expr::BVMul(xs.iter().map(|x| inline_helpers(x,fns,depth+1)).collect::<Result<Vec<_>,_>>()?)),

        Expr::BVUDiv(a,b)=> Ok(Expr::BVUDiv(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVURem(a,b)=> Ok(Expr::BVURem(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVSDiv(a,b)=> Ok(Expr::BVSDiv(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVSRem(a,b)=> Ok(Expr::BVSRem(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVSMod(a,b)=> Ok(Expr::BVSMod(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),

        Expr::BVShl (a,b)=> Ok(Expr::BVShl (Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVLshr(a,b)=> Ok(Expr::BVLshr(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVAshr(a,b)=> Ok(Expr::BVAshr(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),

        Expr::Concat(xs) => Ok(Expr::Concat(xs.iter().map(|x| inline_helpers(x,fns,depth+1)).collect::<Result<Vec<_>,_>>()?)),
        Expr::ZeroExtend{k,e} => Ok(Expr::ZeroExtend{ k:*k, e:Box::new(inline_helpers(e,fns,depth+1)?) }),
        Expr::SignExtend{k,e} => Ok(Expr::SignExtend{ k:*k, e:Box::new(inline_helpers(e,fns,depth+1)?) }),

        Expr::BVUlt(a,b)=> Ok(Expr::BVUlt(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVUle(a,b)=> Ok(Expr::BVUle(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVUgt(a,b)=> Ok(Expr::BVUgt(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVUge(a,b)=> Ok(Expr::BVUge(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVSlt(a,b)=> Ok(Expr::BVSlt(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVSle(a,b)=> Ok(Expr::BVSle(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVSgt(a,b)=> Ok(Expr::BVSgt(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),
        Expr::BVSge(a,b)=> Ok(Expr::BVSge(Box::new(inline_helpers(a,fns,depth+1)?), Box::new(inline_helpers(b,fns,depth+1)?))),

        // leaves
        _ => Ok(e.clone()),
    }
}

// ---------------------------
// Expr -> Z3 AST
// ---------------------------

struct TyCtxt { vars: IndexMap<String, Sort> }

fn bv_from_bits<'ctx>(ctx: &'ctx Context, bits: &str) -> BV<'ctx> {
    let width = bits.len() as u32;
    let mut v: i64 = 0;
    for c in bits.chars() { v = (v << 1) | if c == '1' { 1 } else { 0 }; }
    BV::from_i64(ctx, v, width)
}

fn expr_to_ast<'ctx>(
    e: &Expr,
    ctx: &'ctx Context,
    st: &IndexMap<&'ctx str, Dynamic<'ctx>>,
) -> Result<Dynamic<'ctx>, String> {
    match e {
        Expr::Sym(s) => {
            let key: &'static str = Box::leak(s.clone().into_boxed_str());
            st.get(key).cloned().ok_or_else(|| format!("Unknown symbol: {}", s))
        }
        Expr::BoolConst(b) => Ok(Bool::from_bool(ctx, *b).into()),
        Expr::IntConst(i)  => Ok(Int::from_i64(ctx, *i).into()),
        Expr::BVConst{bits} => Ok(bv_from_bits(ctx, bits).into()),

        Expr::Eq(a,b) => {
            let da = expr_to_ast(a,ctx,st)?; let db = expr_to_ast(b,ctx,st)?;
            if let (Some(x), Some(y)) = (da.as_bool(), db.as_bool()) { Ok(x._eq(&y).into()) }
            else if let (Some(x), Some(y)) = (da.as_int(), db.as_int()) { Ok(x._eq(&y).into()) }
            else if let (Some(x), Some(y)) = (da.as_bv(), db.as_bv())   { Ok(x._eq(&y).into()) }
            else { Err("Type mismatch in '='".into()) }
        }
        Expr::Ite(c, t, e2) => {
            let bc = expr_to_ast(c, ctx, st)?.as_bool().ok_or("ITE cond not Bool")?;
            let dt = expr_to_ast(t, ctx, st)?;
            let de = expr_to_ast(e2, ctx, st)?;
            if let (Some(tt), Some(ee)) = (dt.as_bool(), de.as_bool()) {
                Ok(Bool::ite(&bc, &tt, &ee).into())
            } else if let (Some(tt), Some(ee)) = (dt.as_int(), de.as_int()) {
                Ok(Bool::ite(&bc, &tt, &ee).into())
            } else if let (Some(tt), Some(ee)) = (dt.as_bv(), de.as_bv()) {
                Ok(Bool::ite(&bc, &tt, &ee).into())
            } else {
                Err("ITE branches have different types".into())
            }
        }
        Expr::Extract{hi,lo,e} => {
            let bv = expr_to_ast(e,ctx,st)?.as_bv().ok_or("extract on non-BV")?;
            Ok(bv.extract(*hi,*lo).into())
        }
        Expr::And(xs) => {
            let mut bs: Vec<Bool> = Vec::new();
            for x in xs { bs.push(expr_to_ast(x,ctx,st)?.as_bool().ok_or("and arg not Bool")?); }
            let refs: Vec<&Bool> = bs.iter().collect();
            Ok(Bool::and(ctx, &refs).into())
        }
        Expr::Or(xs) => {
            let mut bs: Vec<Bool> = Vec::new();
            for x in xs { bs.push(expr_to_ast(x,ctx,st)?.as_bool().ok_or("or arg not Bool")?); }
            let refs: Vec<&Bool> = bs.iter().collect();
            Ok(Bool::or(ctx, &refs).into())
        }
        Expr::Xor(xs) => {
            // boolean xor via left fold using != (i.e., not equal)
            if xs.is_empty() {
                return Err("xor expects at least 1 argument".into());
            }
            let mut bs: Vec<Bool> = Vec::with_capacity(xs.len());
            for x in xs {
                let b = expr_to_ast(x, ctx, st)?.as_bool().ok_or("xor arg not Bool")?;
                bs.push(b);
            }
            // (xor a) == a; (xor a b c) == ((a != b) != c) ...
            let mut acc = bs[0].clone();
            for b in bs.iter().skip(1) {
                acc = acc._eq(b).not();
            }
            Ok(acc.into())
        }
        Expr::BVXor(xs) => {
            if xs.len() < 2 {
                return Err("bvxor expects at least 2 arguments".into());
            }
            let mut it = xs.iter();
            let first = expr_to_ast(it.next().unwrap(), ctx, st)?.as_bv().ok_or("bvxor arg not BV")?;
            let mut acc = first;
            for x in it {
                let bv = expr_to_ast(x, ctx, st)?.as_bv().ok_or("bvxor arg not BV")?;
                acc = acc.bvxor(&bv);
            }
            Ok(acc.into())
        }        
        Expr::Not(x) => Ok(expr_to_ast(x,ctx,st)?.as_bool().ok_or("not arg not Bool")?.not().into()),
        Expr::BVAnd(xs) => {
            if xs.len() < 2 { return Err("bvand expects >=2 args".into()); }
            let mut it = xs.iter();
            let mut acc = expr_to_ast(it.next().unwrap(), ctx, st)?.as_bv().ok_or("bvand arg not BV")?;
            for x in it {
                let b = expr_to_ast(x, ctx, st)?.as_bv().ok_or("bvand arg not BV")?;
                acc = acc.bvand(&b);
            }
            Ok(acc.into())
        }
        Expr::BVOr(xs) => {
            if xs.len() < 2 { return Err("bvor expects >=2 args".into()); }
            let mut it = xs.iter();
            let mut acc = expr_to_ast(it.next().unwrap(), ctx, st)?.as_bv().ok_or("bvor arg not BV")?;
            for x in it {
                let b = expr_to_ast(x, ctx, st)?.as_bv().ok_or("bvor arg not BV")?;
                acc = acc.bvor(&b);
            }
            Ok(acc.into())
        }
        Expr::BVNot(x) => {
            let a = expr_to_ast(x, ctx, st)?.as_bv().ok_or("bvnot arg not BV")?;
            Ok(a.bvnot().into())
        }
        Expr::BVNeg(x) => {
            let a = expr_to_ast(x, ctx, st)?.as_bv().ok_or("bvneg arg not BV")?;
            Ok(a.bvneg().into())
        }
        
        Expr::BVAdd(xs) => {
            if xs.len() < 2 { return Err("bvadd expects >=2 args".into()); }
            let mut it = xs.iter();
            let mut acc = expr_to_ast(it.next().unwrap(), ctx, st)?.as_bv().ok_or("bvadd arg not BV")?;
            for x in it {
                let b = expr_to_ast(x, ctx, st)?.as_bv().ok_or("bvadd arg not BV")?;
                acc = acc.bvadd(&b);
            }
            Ok(acc.into())
        }
        Expr::BVSub(a,b) => {
            let aa = expr_to_ast(a, ctx, st)?.as_bv().ok_or("bvsub arg not BV")?;
            let bb = expr_to_ast(b, ctx, st)?.as_bv().ok_or("bvsub arg not BV")?;
            Ok(aa.bvsub(&bb).into())
        }
        Expr::BVMul(xs) => {
            if xs.len() < 2 { return Err("bvmul expects >=2 args".into()); }
            let mut it = xs.iter();
            let mut acc = expr_to_ast(it.next().unwrap(), ctx, st)?.as_bv().ok_or("bvmul arg not BV")?;
            for x in it {
                let b = expr_to_ast(x, ctx, st)?.as_bv().ok_or("bvmul arg not BV")?;
                acc = acc.bvmul(&b);
            }
            Ok(acc.into())
        }
        
        Expr::BVUDiv(a,b) => {
            let aa = expr_to_ast(a, ctx, st)?.as_bv().ok_or("bvudiv arg not BV")?;
            let bb = expr_to_ast(b, ctx, st)?.as_bv().ok_or("bvudiv arg not BV")?;
            Ok(aa.bvudiv(&bb).into())
        }
        Expr::BVURem(a,b) => {
            let aa = expr_to_ast(a, ctx, st)?.as_bv().ok_or("bvurem arg not BV")?;
            let bb = expr_to_ast(b, ctx, st)?.as_bv().ok_or("bvurem arg not BV")?;
            Ok(aa.bvurem(&bb).into())
        }
        Expr::BVSDiv(a,b) => {
            let aa = expr_to_ast(a, ctx, st)?.as_bv().ok_or("bvsdiv arg not BV")?;
            let bb = expr_to_ast(b, ctx, st)?.as_bv().ok_or("bvsdiv arg not BV")?;
            Ok(aa.bvsdiv(&bb).into())
        }
        Expr::BVSRem(a,b) => {
            let aa = expr_to_ast(a, ctx, st)?.as_bv().ok_or("bvsrem arg not BV")?;
            let bb = expr_to_ast(b, ctx, st)?.as_bv().ok_or("bvsrem arg not BV")?;
            Ok(aa.bvsrem(&bb).into())
        }
        Expr::BVSMod(a,b) => {
            let aa = expr_to_ast(a, ctx, st)?.as_bv().ok_or("bvsmod arg not BV")?;
            let bb = expr_to_ast(b, ctx, st)?.as_bv().ok_or("bvsmod arg not BV")?;
            Ok(aa.bvsmod(&bb).into())
        }
        
        Expr::BVShl(a,b) => {
            let aa = expr_to_ast(a, ctx, st)?.as_bv().ok_or("bvshl arg not BV")?;
            let bb = expr_to_ast(b, ctx, st)?.as_bv().ok_or("bvshl shift not BV")?;
            Ok(aa.bvshl(&bb).into())
        }
        Expr::BVLshr(a,b) => {
            let aa = expr_to_ast(a, ctx, st)?.as_bv().ok_or("bvlshr arg not BV")?;
            let bb = expr_to_ast(b, ctx, st)?.as_bv().ok_or("bvlshr shift not BV")?;
            Ok(aa.bvlshr(&bb).into())
        }
        Expr::BVAshr(a,b) => {
            let aa = expr_to_ast(a, ctx, st)?.as_bv().ok_or("bvashr arg not BV")?;
            let bb = expr_to_ast(b, ctx, st)?.as_bv().ok_or("bvashr shift not BV")?;
            Ok(aa.bvashr(&bb).into())
        }
        
        Expr::Concat(xs) => {
            if xs.len() < 2 { return Err("concat expects >=2 args".into()); }
            let mut it = xs.iter();
            let mut acc = expr_to_ast(it.next().unwrap(), ctx, st)?.as_bv().ok_or("concat arg not BV")?;
            for x in it {
                let b = expr_to_ast(x, ctx, st)?.as_bv().ok_or("concat arg not BV")?;
                acc = acc.concat(&b);
            }
            Ok(acc.into())
        }
        Expr::ZeroExtend{k, e} => {
            let a = expr_to_ast(e, ctx, st)?.as_bv().ok_or("zero_extend arg not BV")?;
            Ok(a.zero_ext(*k).into())
        }
        Expr::SignExtend{k, e} => {
            let a = expr_to_ast(e, ctx, st)?.as_bv().ok_or("sign_extend arg not BV")?;
            Ok(a.sign_ext(*k).into())
        }
        
        Expr::BVUlt(a,b) => {
            let aa = expr_to_ast(a, ctx, st)?.as_bv().ok_or("bvult arg not BV")?;
            let bb = expr_to_ast(b, ctx, st)?.as_bv().ok_or("bvult arg not BV")?;
            Ok(aa.bvult(&bb).into())
        }
        Expr::BVUle(a,b) => { let aa=expr_to_ast(a,ctx,st)?.as_bv().ok_or("bvule arg not BV")?;
                              let bb=expr_to_ast(b,ctx,st)?.as_bv().ok_or("bvule arg not BV")?;
                              Ok(aa.bvule(&bb).into()) }
        Expr::BVUgt(a,b) => { let aa=expr_to_ast(a,ctx,st)?.as_bv().ok_or("bvugt arg not BV")?;
                              let bb=expr_to_ast(b,ctx,st)?.as_bv().ok_or("bvugt arg not BV")?;
                              Ok(aa.bvugt(&bb).into()) }
        Expr::BVUge(a,b) => { let aa=expr_to_ast(a,ctx,st)?.as_bv().ok_or("bvuge arg not BV")?;
                              let bb=expr_to_ast(b,ctx,st)?.as_bv().ok_or("bvuge arg not BV")?;
                              Ok(aa.bvuge(&bb).into()) }
        Expr::BVSlt(a,b) => { let aa=expr_to_ast(a,ctx,st)?.as_bv().ok_or("bvslt arg not BV")?;
                              let bb=expr_to_ast(b,ctx,st)?.as_bv().ok_or("bvslt arg not BV")?;
                              Ok(aa.bvslt(&bb).into()) }
        Expr::BVSle(a,b) => { let aa=expr_to_ast(a,ctx,st)?.as_bv().ok_or("bvsle arg not BV")?;
                              let bb=expr_to_ast(b,ctx,st)?.as_bv().ok_or("bvsle arg not BV")?;
                              Ok(aa.bvsle(&bb).into()) }
        Expr::BVSgt(a,b) => { let aa=expr_to_ast(a,ctx,st)?.as_bv().ok_or("bvsgt arg not BV")?;
                              let bb=expr_to_ast(b,ctx,st)?.as_bv().ok_or("bvsgt arg not BV")?;
                              Ok(aa.bvsgt(&bb).into()) }
        Expr::BVSge(a,b) => { let aa=expr_to_ast(a,ctx,st)?.as_bv().ok_or("bvsge arg not BV")?;
                              let bb=expr_to_ast(b,ctx,st)?.as_bv().ok_or("bvsge arg not BV")?;
                              Ok(aa.bvsge(&bb).into()) }
                              Expr::Distinct(xs) => {
                                match xs.len() {
                                    0 | 1 => Ok(Bool::from_bool(ctx, true).into()),
                                    _ => {
                                        let ds: Vec<Dynamic> = xs.iter()
                                            .map(|x| expr_to_ast(x, ctx, st))
                                            .collect::<Result<_, _>>()?;
                                        let refs: Vec<&Dynamic> = ds.iter().collect();
                            
                                        Ok(Dynamic::distinct(ctx, &refs).into())
                                    }
                                }
                            }
                            
                            
                            
        Expr::App(name, _args) => Err(format!("Unexpected raw App({}) after inlining; missing helper def?", name)),
    }
}

// ---------------------------
// ITE decomposition
// ---------------------------

fn collect_ite_pairs(e: &Expr) -> Vec<(Expr, Expr)> {
    fn go(e: &Expr, path: Expr, out: &mut Vec<(Expr, Expr)>) {
        match e {
            Expr::Ite(c, t, f) => {
                let g_then = Expr::And(vec![path.clone(), (*c.clone())]);
                let g_else = Expr::And(vec![path, Expr::Not(Box::new((*c.clone())))]);
                go(t, g_then, out);
                go(f, g_else, out);
            }
            _ => out.push((Expr::And(vec![path, Expr::BoolConst(true)]), e.clone())), // normalize
        }
    }
    let mut out = Vec::new();
    go(e, Expr::BoolConst(true), &mut out);
    out
}


fn simplify_guard(e: Expr) -> Expr {
    // Tiny normalizer: and(true, X) => X; and() => true; or() => false; not(not x) => x
    match e {
        Expr::And(mut xs) => {
            let mut flat = Vec::new();
            for x in xs.drain(..) {
                match simplify_guard(x) {
                    Expr::BoolConst(true) => {}
                    Expr::And(inner) => flat.extend(inner),
                    y => flat.push(y),
                }
            }
            if flat.is_empty() { Expr::BoolConst(true) } else if flat.len()==1 { flat.remove(0) } else { Expr::And(flat) }
        }
        Expr::Or(mut xs) => {
            let mut flat = Vec::new();
            for x in xs.drain(..) {
                match simplify_guard(x) {
                    Expr::BoolConst(false) => {}
                    Expr::Or(inner) => flat.extend(inner),
                    y => flat.push(y),
                }
            }
            if flat.is_empty() { Expr::BoolConst(false) } else if flat.len()==1 { flat.remove(0) } else { Expr::Or(flat) }
        }
        Expr::Not(x) => {
            match *x {
                Expr::Not(xx) => simplify_guard(*xx),
                other => Expr::Not(Box::new(simplify_guard(other))),
            }
        }
        other => other,
    }
}

// ---------------------------
// Top-level: build SMVEnv
// ---------------------------

fn leak_str(s: &str) -> &'static str { Box::leak(s.to_string().into_boxed_str()) }

pub fn build_env_from_flat_smt<'ctx>(ctx: &'ctx Context, smt: &str) -> Result<SMVEnv<'ctx>, String> {
    let sexps = parse_sexps(smt)?;

    struct Decl { name: String, sort: Sort }
    struct NextDef { var: String, ret: Sort, body: Expr }
    struct InitDef { var: String, ret: Sort, body: Expr }

    let mut decls: Vec<Decl> = Vec::new();
    let mut fns:   FnTable   = IndexMap::new();
    let mut nexts: Vec<NextDef> = Vec::new();
    let mut inits: Vec<InitDef> = Vec::new();

    let mut total_transitions: usize = 0;

    for top in sexps {
        let items = match top { SExp::List(v) => v, _ => continue };
        if items.is_empty() { continue; }
        let head = match &items[0] { SExp::Atom(a) => a.as_str(), _ => continue };

        match head {
            "declare-const" => {
                if items.len() != 3 { return Err("declare-const arity".into()); }
                let name = strip_pipes(&items[1].as_atom().ok_or("declare-const name")?);
                let sort = parse_sort(&items[2])?;
                decls.push(Decl { name, sort });
            }
            "define-fun" => {
                if items.len() != 5 { return Err("define-fun arity".into()); }
                let raw = strip_pipes(&items[1].as_atom().ok_or("define-fun name")?);

                // params: list of (name, sort)
                let mut params = Vec::new();
                let param_list = match &items[2] { SExp::List(v) => v, _ => return Err("params must be list".into()) };
                for p in param_list {
                    let pair = match p { SExp::List(v) => v, _ => return Err("param pair".into()) };
                    if pair.len() != 2 { return Err("param pair arity".into()); }
                    let pname = strip_pipes(&pair[0].as_atom().ok_or("param name")?);
                    let psort = parse_sort(&pair[1])?;
                    params.push((pname, psort));
                }

                let ret = parse_sort(&items[3])?;
                let body = parse_expr(&items[4])?;

                if raw.starts_with("next ") {
                    nexts.push(NextDef { var: raw["next ".len()..].to_string(), ret, body });
                } else if raw.starts_with("init ") {
                    inits.push(InitDef { var: raw["init ".len()..].to_string(), ret, body });
                } else {
                    // helper
                    fns.insert(raw, FnDef { params, ret, body });
                }
            }
            _ => {}
        }
    }

    // Build env & auto-bounds for BV (signed full range to match bvsge/bvsle in your env)
    let mut env = SMVEnv::new(ctx);
    for d in &decls {
        let nm: &'static str = leak_str(&d.name);
        match d.sort {
            Sort::Bool => env.register_variable(nm, VarType::Bool { init: None }),
            Sort::Int  => env.register_variable(nm, VarType::Int  { init: None, lower: None, upper: None }),
            Sort::BV(w) => {
                // Unsigned domain: [0, 2^w - 1]. Only set upper when it fits in i64.
                let lo = Some(0i64);
                let hi = if w <= 63 {
                    Some(((1u128 << w) - 1) as i64) // fits up to 2^63-1
                } else {
                    None // leave unbounded if it wouldn't fit into i64
                };
                // unbounded gives marginally
                env.register_variable(nm, VarType::BVector { width: w, lower: lo, upper: hi, init: None });
            }
        }
        
    }

    // Apply INITs (still expect constants)
    for i in &inits {
        let nm: &'static str = leak_str(&i.var);
        let vt = env.get_variable_type(nm).ok_or_else(|| format!("init for undeclared {}", i.var))?.clone();
        match (vt, &i.ret) {
            (VarType::Bool{..}, Sort::Bool) => {
                let val = match &i.body { Expr::BoolConst(b) => *b, _ => return Err(format!("init {} must be Bool const", i.var)) };
                if let Some(v) = env.get_variable_mut(nm) {
                    *v = Variable { sort: VarType::Bool { init: Some(vec![val]) } };
                }
            }
            (VarType::Int{..}, Sort::Int) => {
                let val = match &i.body { Expr::IntConst(k) => *k, _ => return Err(format!("init {} must be Int const", i.var)) };
                if let Some(v) = env.get_variable_mut(nm) {
                    *v = Variable { sort: VarType::Int { init: Some(vec![val]), lower: None, upper: None } };
                }
            }
            (VarType::BVector{width, ..}, Sort::BV(_)) => {
                let bits = match &i.body { Expr::BVConst{bits} => bits.clone(), _ => return Err(format!("init {} must be BV const", i.var)) };
                // convert to i64
                let bv = bv_from_bits(ctx, &bits);
                let as_u = bv.as_u64().unwrap_or(0);
                if let Some(v) = env.get_variable_mut(nm) {
                    *v = Variable { sort: VarType::BVector { width, lower: v.sort_lower(), upper: v.sort_upper(), init: Some(vec![as_u as i64]) } };
                }
            }
            _ => return Err(format!("init {} sort mismatch", i.var)),
        }
    }

    // Helper to re-use existing bounds when overwriting Variable
    trait BoundsExt { fn sort_lower(&self) -> Option<i64>; fn sort_upper(&self) -> Option<i64>; }
    impl BoundsExt for Variable {
        fn sort_lower(&self) -> Option<i64> { match self.sort { VarType::BVector{lower, ..} => lower, _ => None } }
        fn sort_upper(&self) -> Option<i64> { match self.sort { VarType::BVector{upper, ..} => upper, _ => None } }
    }

    // Register transitions from NEXT defs:
    //  - inline helpers in the next-body
    //  - decompose ITEs into (guard, rhs) pairs
    //  - for each pair, register_transition(var, guard, update)
    for n in &nexts {
        let var_nm: &'static str = leak_str(&n.var);
    
        // 1) Inline helpers on-demand with memoization (fast & shared)
        let mut memo = InlineMemo::default();
        let inlined = inline_helpers_memo(&n.body, &fns, &mut memo)?;
    
        // 2) Decompose into disjoint (guard, rhs) pairs
        //let pairs = collect_ite_pairs_smart(&inlined);
        let pairs = explode_all_ites_factored(&inlined);

        
    
        // 3) Register each pair as a transition (guards/updates are arbitrary ASTs)
        // 3) Print & register each pair as a transition (guards/updates are arbitrary ASTs)
        {
            // Create a stable dummy state once per target variable (nice names for printing)
            let dbg_state = env.make_dummy_state(ctx);

            for (rule_idx, (g_expr, rhs_expr)) in pairs.into_iter().enumerate() {
                // --- DEBUG: compile to Z3 and print before registering ---
                let g_dyn = match expr_to_ast(&g_expr, ctx, &dbg_state) {
                    Ok(x) => x,
                    Err(e) => {
                        eprintln!(
                            "[IR DEBUG] Guard compile error for `{}` rule {}: {}\n  LHS expr: {}",
                            var_nm, rule_idx, e, fmt_expr(&g_expr)
                        );
                        panic!("guard translation failed");
                    }
                };
                let g_bool = match g_dyn.as_bool() {
                    Some(b) => b,
                    None => {
                        eprintln!(
                            "[IR DEBUG] Guard is not Bool for `{}` rule {}.\n  LHS expr: {}",
                            var_nm, rule_idx, fmt_expr(&g_expr)
                        );
                        panic!("guard must be Bool");
                    }
                };

                let rhs_dyn = match expr_to_ast(&rhs_expr, ctx, &dbg_state) {
                    Ok(x) => x,
                    Err(e) => {
                        eprintln!(
                            "[IR DEBUG] Update compile error for `{}` rule {}: {}\n  RHS expr: {}",
                            var_nm, rule_idx, e, fmt_expr(&rhs_expr)
                        );
                        panic!("rhs translation failed");
                    }
                };

                // Print the actual Z3 ASTs
                /*println!(
                    "[IR DEBUG] {}[{}]: Guard ='{}' -> Update = '{}'",
                    var_nm,
                    rule_idx,
                    g_bool.to_string(),
                    rhs_dyn.to_string()
                );*/

                // --- Register transition (same closures as before) ---
                let g_expr_cloned = g_expr.clone();
                let rhs_expr_cloned = rhs_expr.clone();
                let var_label = var_nm;

                env.register_transition(
                    var_nm,
                    move |_env, ctx, st| {
                        let g_dyn = match expr_to_ast(&g_expr_cloned, ctx, st) {
                            Ok(x) => x,
                            Err(e) => {
                                eprintln!(
                                    "IR error compiling guard (lhs) for variable `{}`: {}\n  LHS expr: {}",
                                    var_label, e, fmt_expr(&g_expr_cloned)
                                );
                                panic!("guard translation failed");
                            }
                        };
                        let g_bool = match g_dyn.as_bool() {
                            Some(b) => b,
                            None => {
                                eprintln!(
                                    "IR error: guard (lhs) is not Bool for variable `{}`.\n  LHS expr: {}",
                                    var_label, fmt_expr(&g_expr_cloned)
                                );
                                panic!("guard must be Bool");
                            }
                        };
                        ReturnType::DynAst(g_bool.into())
                    },
                    move |_env, ctx, st| {
                        let dyn_ast = match expr_to_ast(&rhs_expr_cloned, ctx, st) {
                            Ok(x) => x,
                            Err(e) => {
                                eprintln!(
                                    "IR error compiling update (rhs) for variable `{}`: {}\n  RHS expr: {}",
                                    var_label, e, fmt_expr(&rhs_expr_cloned)
                                );
                                panic!("rhs translation failed");
                            }
                        };
                        ReturnType::DynAst(dyn_ast)
                    }
                );
                total_transitions += 1;
            }
        } // dbg_state drops here


        // NOTE: We do NOT rely on stutter default; the pairs cover all cases from the ITEs.
    }
    eprintln!("[IR] Built SMVEnv with {} total transitions", total_transitions);
    Ok(env)
}


fn fmt_expr(e: &Expr) -> String {
    fn join(xs: &[String]) -> String { xs.join(" ") }
    match e {
        Expr::Sym(s) => s.clone(),
        Expr::BoolConst(b) => if *b { "true".into() } else { "false".into() },
        Expr::IntConst(i) => i.to_string(),
        Expr::BVConst { bits } => format!("#b{}", bits),
        Expr::Eq(a,b) => format!("(= {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::Ite(c,t,f) => format!("(ite {} {} {})", fmt_expr(c), fmt_expr(t), fmt_expr(f)),
        Expr::Extract { hi, lo, e } =>
            format!("((_ extract {} {}) {})", hi, lo, fmt_expr(e)),
        Expr::And(xs) => format!("(and {})", join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),
        Expr::Or(xs)  => format!("(or {})",  join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),
        Expr::Not(x)  => format!("(not {})", fmt_expr(x)),
        Expr::Xor(xs)   => format!("(xor {})",   join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),
        Expr::BVXor(xs) => format!("(bvxor {})", join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),
        Expr::BVAnd(xs) => format!("(bvand {})", join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),
        Expr::BVOr(xs)  => format!("(bvor {})",  join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),
        Expr::BVNot(x)  => format!("(bvnot {})", fmt_expr(x)),
        Expr::BVNeg(x)  => format!("(bvneg {})", fmt_expr(x)),

        Expr::BVAdd(xs) => format!("(bvadd {})", join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),
        Expr::BVSub(a,b)=> format!("(bvsub {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::BVMul(xs) => format!("(bvmul {})", join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),
        Expr::BVUDiv(a,b)=> format!("(bvudiv {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::BVURem(a,b)=> format!("(bvurem {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::BVSDiv(a,b)=> format!("(bvsdiv {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::BVSRem(a,b)=> format!("(bvsrem {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::BVSMod(a,b)=> format!("(bvsmod {} {})", fmt_expr(a), fmt_expr(b)),

        Expr::BVShl(a,b)  => format!("(bvshl {} {})",  fmt_expr(a), fmt_expr(b)),
        Expr::BVLshr(a,b) => format!("(bvlshr {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::BVAshr(a,b) => format!("(bvashr {} {})", fmt_expr(a), fmt_expr(b)),

        Expr::Concat(xs)  => format!("(concat {})", join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),
        Expr::ZeroExtend{k,e} => format!("((_ zero_extend {}) {})", k, fmt_expr(e)),
        Expr::SignExtend{k,e} => format!("((_ sign_extend {}) {})", k, fmt_expr(e)),

        Expr::BVUlt(a,b)=> format!("(bvult {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::BVUle(a,b)=> format!("(bvule {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::BVUgt(a,b)=> format!("(bvugt {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::BVUge(a,b)=> format!("(bvuge {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::BVSlt(a,b)=> format!("(bvslt {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::BVSle(a,b)=> format!("(bvsle {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::BVSgt(a,b)=> format!("(bvsgt {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::BVSge(a,b)=> format!("(bvsge {} {})", fmt_expr(a), fmt_expr(b)),
        Expr::Distinct(xs) => format!("(distinct {})", join(&xs.iter().map(fmt_expr).collect::<Vec<_>>())),

        Expr::App(name, args) =>
            format!("({} {})", name, join(&args.iter().map(fmt_expr).collect::<Vec<_>>())),
    }
}



use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

// ---------- Structural fingerprint (no trait impls needed) ----------
fn fp_u64(mut h: u64, x: u64) -> u64 { // FNV-1a style mix (simple and fast)
    const P: u64 = 0x100000001b3;
    h ^= x;
    h = h.wrapping_mul(P);
    h
}
fn fp_bytes(mut h: u64, bs: &[u8]) -> u64 {
    for &b in bs { h = fp_u64(h, b as u64); }
    h
}
use std::cmp::Ordering;

/// Deterministic 64-bit FNV-1a
#[inline]
fn fnv1a_mix_u64(state: &mut u64, x: u64) {
    const FNV_PRIME: u64 = 0x0000_0001_0000_01B3;
    *state ^= x;
    *state = state.wrapping_mul(FNV_PRIME);
}
#[inline]
fn fnv1a_mix_bytes(state: &mut u64, bs: &[u8]) {
    const FNV_PRIME: u64 = 0x0000_0001_0000_01B3;
    for &b in bs {
        *state ^= b as u64;
        *state = state.wrapping_mul(FNV_PRIME);
    }
}
#[inline]
fn hash_str_d64(s: &str) -> u64 {
    let mut st: u64 = 0xCBF2_9CE4_8422_2325;
    fnv1a_mix_bytes(&mut st, s.as_bytes());
    st
}
#[inline]
fn combine_tag_parts(tag: &str, parts: &[u64]) -> u64 {
    let mut st: u64 = 0xCBF2_9CE4_8422_2325;
    fnv1a_mix_bytes(&mut st, tag.as_bytes());
    fnv1a_mix_u64(&mut st, parts.len() as u64);
    for &p in parts { fnv1a_mix_u64(&mut st, p); }
    st
}
#[inline]
fn combine2(tag: &str, first: u64, rest: &[u64]) -> u64 {
    let mut parts = Vec::with_capacity(1 + rest.len());
    parts.push(first);
    parts.extend_from_slice(rest);
    combine_tag_parts(tag, &parts)
}

pub fn fingerprint_expr(e: &Expr) -> u64 {
    fn go(e: &Expr) -> u64 {
        match e {
            Expr::Sym(s)            => combine2("Sym", hash_str_d64(s), &[]),
            Expr::BoolConst(b)      => combine_tag_parts("BoolConst", &[if *b {1} else {0}]),
            Expr::IntConst(i)       => combine_tag_parts("IntConst", &[*i as u64]),
            Expr::BVConst { bits }  => combine2("BVConst", hash_str_d64(bits), &[]),

            Expr::Eq(a, b) => {
                // canonicalize equality (commutative)
                let mut xs = [go(a), go(b)];
                xs.sort_unstable();
                combine_tag_parts("Eq", &xs)
            }
            Expr::Ite(c, t, f) => combine_tag_parts("Ite", &[go(c), go(t), go(f)]),

            Expr::Extract { hi, lo, e } =>
                combine_tag_parts("Extract", &[*hi as u64, *lo as u64, go(e)]),

            // Boolean connectives (AC)
            Expr::And(xs) => {
                let mut ps: Vec<u64> = xs.iter().map(go).collect();
                ps.sort_unstable();
                combine_tag_parts("And", &ps)
            }
            Expr::Or(xs) => {
                let mut ps: Vec<u64> = xs.iter().map(go).collect();
                ps.sort_unstable();
                combine_tag_parts("Or", &ps)
            }
            Expr::Not(x) => combine_tag_parts("Not", &[go(x)]),

            // XORs are AC
            Expr::Xor(xs) => {
                let mut ps: Vec<u64> = xs.iter().map(go).collect();
                ps.sort_unstable();
                combine_tag_parts("Xor", &ps)
            }
            Expr::BVXor(xs) => {
                let mut ps: Vec<u64> = xs.iter().map(go).collect();
                ps.sort_unstable();
                combine_tag_parts("BVXor", &ps)
            }

            // ==== New BV ops ====

            // AC families
            Expr::BVAnd(xs) => {
                let mut ps: Vec<u64> = xs.iter().map(go).collect();
                ps.sort_unstable();
                combine_tag_parts("BVAnd", &ps)
            }
            Expr::BVOr(xs) => {
                let mut ps: Vec<u64> = xs.iter().map(go).collect();
                ps.sort_unstable();
                combine_tag_parts("BVOr", &ps)
            }
            Expr::BVAdd(xs) => {
                let mut ps: Vec<u64> = xs.iter().map(go).collect();
                ps.sort_unstable();
                combine_tag_parts("BVAdd", &ps)
            }
            Expr::BVMul(xs) => {
                let mut ps: Vec<u64> = xs.iter().map(go).collect();
                ps.sort_unstable();
                combine_tag_parts("BVMul", &ps)
            }
            Expr::Distinct(xs) => {
                let mut ps: Vec<u64> = xs.iter().map(go).collect();
                ps.sort_unstable();                // order-insensitive, duplicates preserved
                combine_tag_parts("Distinct", &ps)
            }
            

            // Unary
            Expr::BVNot(x) => combine_tag_parts("BVNot", &[go(x)]),
            Expr::BVNeg(x) => combine_tag_parts("BVNeg", &[go(x)]),

            // Binary, order-sensitive
            Expr::BVSub(a, b)  => combine_tag_parts("BVSub",  &[go(a), go(b)]),
            Expr::BVUDiv(a, b) => combine_tag_parts("BVUDiv", &[go(a), go(b)]),
            Expr::BVURem(a, b) => combine_tag_parts("BVURem", &[go(a), go(b)]),
            Expr::BVSDiv(a, b) => combine_tag_parts("BVSDiv", &[go(a), go(b)]),
            Expr::BVSRem(a, b) => combine_tag_parts("BVSRem", &[go(a), go(b)]),
            Expr::BVSMod(a, b) => combine_tag_parts("BVSMod", &[go(a), go(b)]),

            Expr::BVShl(a, b)  => combine_tag_parts("BVShl",  &[go(a), go(b)]),
            Expr::BVLshr(a, b) => combine_tag_parts("BVLshr", &[go(a), go(b)]),
            Expr::BVAshr(a, b) => combine_tag_parts("BVAshr", &[go(a), go(b)]),

            // concat is order-sensitive
            Expr::Concat(xs) => {
                let ps: Vec<u64> = xs.iter().map(go).collect();
                combine_tag_parts("Concat", &ps)
            }

            // Exts
            Expr::ZeroExtend { k, e } => combine_tag_parts("ZeroExtend", &[*k as u64, go(e)]),
            Expr::SignExtend { k, e } => combine_tag_parts("SignExtend", &[*k as u64, go(e)]),

            // BV comparisons (Bool-valued, order-sensitive)
            Expr::BVUlt(a, b) => combine_tag_parts("BVUlt", &[go(a), go(b)]),
            Expr::BVUle(a, b) => combine_tag_parts("BVUle", &[go(a), go(b)]),
            Expr::BVUgt(a, b) => combine_tag_parts("BVUgt", &[go(a), go(b)]),
            Expr::BVUge(a, b) => combine_tag_parts("BVUge", &[go(a), go(b)]),
            Expr::BVSlt(a, b) => combine_tag_parts("BVSlt", &[go(a), go(b)]),
            Expr::BVSle(a, b) => combine_tag_parts("BVSle", &[go(a), go(b)]),
            Expr::BVSgt(a, b) => combine_tag_parts("BVSgt", &[go(a), go(b)]),
            Expr::BVSge(a, b) => combine_tag_parts("BVSge", &[go(a), go(b)]),

            // Should not persist after inlining, but keep a stable fp
            Expr::App(name, args) => {
                let mut parts: Vec<u64> = Vec::with_capacity(1 + args.len());
                parts.push(hash_str_d64(name));
                parts.extend(args.iter().map(go));
                combine_tag_parts("App", &parts)
            }
        }
    }
    go(e)
}



// ---------- Memoized helper inliner (apps → bodies), high-performance ----------


pub fn inline_helpers_memo(
    e: &Expr,
    fns: &FnTable,
    memo: &mut InlineMemo,
) -> Result<Expr, String> {
    fn go(
        e: &Expr,
        fns: &FnTable,
        memo: &mut InlineMemo,
        depth: usize,
    ) -> Result<Expr, String> {
        if depth > 512 {
            return Err("helper expansion depth exceeded".into());
        }
        match e {
            // --- Inline helper applications with memoization ---
            Expr::App(name, args) if fns.contains_key(name) => {
                let def = &fns[name];
                if def.params.len() != args.len() {
                    return Err(format!(
                        "arity mismatch in call {}: expected {}, got {}",
                        name, def.params.len(), args.len()
                    ));
                }

                // 1) Inline arguments first
                let mut inlined_args = Vec::with_capacity(args.len());
                for a in args {
                    inlined_args.push(go(a, fns, memo, depth + 1)?);
                }

                // 2) Build memo key from helper name + arg fingerprints
                let fp_args: Vec<u64> = inlined_args.iter().map(fingerprint_expr).collect();
                let key: InlineKey = (name.clone(), fp_args);

                // 3) Return memoized result if available
                if let Some(hit) = memo.get(&key) {
                    return Ok(hit.clone());
                }

                // 4) Substitute formals with inlined actuals
                let mut sub = IndexMap::<String, Expr>::new();
                for ((p, _psort), act) in def.params.iter().zip(inlined_args.into_iter()) {
                    sub.insert(p.clone(), act);
                }
                let body_sub = subst_expr(&def.body, &sub);

                // 5) Recurse to inline helpers inside the substituted body
                let res = go(&body_sub, fns, memo, depth + 1)?;

                // 6) Memoize and return
                memo.insert(key, res.clone());
                Ok(res)
            }

            // --- Recurse structurally through all other nodes ---
            Expr::Eq(a, b) => Ok(Expr::Eq(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::Ite(c, t, f) => Ok(Expr::Ite(
                Box::new(go(c, fns, memo, depth + 1)?),
                Box::new(go(t, fns, memo, depth + 1)?),
                Box::new(go(f, fns, memo, depth + 1)?),
            )),
            Expr::Extract { hi, lo, e } => Ok(Expr::Extract {
                hi: *hi,
                lo: *lo,
                e: Box::new(go(e, fns, memo, depth + 1)?),
            }),

            Expr::And(xs) => Ok(Expr::And(
                xs.iter()
                    .map(|x| go(x, fns, memo, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Expr::Or(xs) => Ok(Expr::Or(
                xs.iter()
                    .map(|x| go(x, fns, memo, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Expr::Not(x) => Ok(Expr::Not(Box::new(go(x, fns, memo, depth + 1)?))),
            Expr::Xor(xs) => Ok(Expr::Xor(
                xs.iter()
                    .map(|x| go(x, fns, memo, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Expr::BVXor(xs) => Ok(Expr::BVXor(
                xs.iter()
                    .map(|x| go(x, fns, memo, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?,
            )),

            // === New BV nodes (structural recursion only) ===
            Expr::BVAnd(xs) => Ok(Expr::BVAnd(
                xs.iter()
                    .map(|x| go(x, fns, memo, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Expr::BVOr(xs) => Ok(Expr::BVOr(
                xs.iter()
                    .map(|x| go(x, fns, memo, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Expr::BVNot(x) => Ok(Expr::BVNot(Box::new(go(x, fns, memo, depth + 1)?))),
            Expr::BVNeg(x) => Ok(Expr::BVNeg(Box::new(go(x, fns, memo, depth + 1)?))),

            Expr::BVAdd(xs) => Ok(Expr::BVAdd(
                xs.iter()
                    .map(|x| go(x, fns, memo, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Expr::BVSub(a, b) => Ok(Expr::BVSub(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVMul(xs) => Ok(Expr::BVMul(
                xs.iter()
                    .map(|x| go(x, fns, memo, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?,
            )),

            Expr::BVUDiv(a, b) => Ok(Expr::BVUDiv(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVURem(a, b) => Ok(Expr::BVURem(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVSDiv(a, b) => Ok(Expr::BVSDiv(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVSRem(a, b) => Ok(Expr::BVSRem(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVSMod(a, b) => Ok(Expr::BVSMod(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),

            Expr::BVShl(a, b) => Ok(Expr::BVShl(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVLshr(a, b) => Ok(Expr::BVLshr(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVAshr(a, b) => Ok(Expr::BVAshr(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),

            Expr::Concat(xs) => Ok(Expr::Concat(
                xs.iter()
                    .map(|x| go(x, fns, memo, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Expr::ZeroExtend { k, e } => Ok(Expr::ZeroExtend {
                k: *k,
                e: Box::new(go(e, fns, memo, depth + 1)?),
            }),
            Expr::SignExtend { k, e } => Ok(Expr::SignExtend {
                k: *k,
                e: Box::new(go(e, fns, memo, depth + 1)?),
            }),

            Expr::BVUlt(a, b) => Ok(Expr::BVUlt(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVUle(a, b) => Ok(Expr::BVUle(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVUgt(a, b) => Ok(Expr::BVUgt(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVUge(a, b) => Ok(Expr::BVUge(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVSlt(a, b) => Ok(Expr::BVSlt(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVSle(a, b) => Ok(Expr::BVSle(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVSgt(a, b) => Ok(Expr::BVSgt(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::BVSge(a, b) => Ok(Expr::BVSge(
                Box::new(go(a, fns, memo, depth + 1)?),
                Box::new(go(b, fns, memo, depth + 1)?),
            )),
            Expr::Distinct(xs) => Ok(Expr::Distinct(
                xs.iter()
                  .map(|x| go(x, fns, memo, depth + 1))
                  .collect::<Result<Vec<_>, _>>()?
            )),
            

            // Leaves / passthroughs
            Expr::App(_, _) => Ok(e.clone()), // not a known helper: leave as-is
            Expr::Sym(_) | Expr::BoolConst(_) | Expr::IntConst(_) | Expr::BVConst{..} => Ok(e.clone()),
        }
    }
    go(e, fns, memo, 0)
}


// ---------- Smart ITE decomposition (skips obviously-false branches) ----------
fn collect_ite_pairs_smart(e: &Expr) -> Vec<(Expr, Expr)> {
    fn go(e: &Expr, path: Expr, out: &mut Vec<(Expr, Expr)>) {
        match e {
            Expr::Ite(c, t, f) => {
                let g_then = simplify_guard(Expr::And(vec![path.clone(), (*c.clone())]));
                let g_else = simplify_guard(Expr::And(vec![path, Expr::Not(Box::new((*c.clone())))]));
                // prune trivially-false guards early
                if !matches!(g_then, Expr::BoolConst(false)) { go(t, g_then, out); }
                if !matches!(g_else, Expr::BoolConst(false)) { go(f, g_else, out); }
            }
            _ => {
                // terminal RHS under current guard
                let g = simplify_guard(path);
                if !matches!(g, Expr::BoolConst(false)) {
                    out.push((g, e.clone()));
                }
            }
        }
    }
    let mut out = Vec::new();
    go(e, Expr::BoolConst(true), &mut out);
    out
}


use std::collections::{HashMap, HashSet};

/// Fully lift all ITEs out of `e`, returning guarded alternatives whose RHSs
/// contain **no Expr::Ite** anywhere. Includes mitigations:
///  - left-to-right combination with early pruning,
///  - skip singletons,
///  - guard factoring on a common condition across children,
///  - contradiction pruning (C ∧ ¬C),
///  - soft cap on intermediate rows (prevents pathologies).
pub fn explode_all_ites_factored(e: &Expr) -> Vec<(Expr, Expr)> {
    const MAX_ROWS: usize = 1 << 14; // 16k; tune if needed

    #[inline] fn t() -> Expr { Expr::BoolConst(true) }
    #[inline] fn f() -> Expr { Expr::BoolConst(false) }

    #[inline]
    fn and_guard(a: Expr, b: Expr) -> Expr {
        simplify_guard(Expr::And(vec![a, b]))
    }

    // ---------- Literal extraction on top-level AND ----------
    // We treat a "literal" as either X or (not X) where X is not And/Or/Not.
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Pol { Pos, Neg }

    #[inline]
    fn is_atomic(x: &Expr) -> bool {
        !matches!(x,
            Expr::And(_) | Expr::Or(_) | Expr::Not(_)
        )
    }

    fn guard_literals(g: &Expr) -> (HashSet<u64>, HashSet<u64>) {
        // returns (pos_set, neg_set) of literal fingerprints
        fn collect<'a>(g: &'a Expr, pos: &mut HashSet<u64>, neg: &mut HashSet<u64>) {
            match g {
                Expr::BoolConst(true) => {}
                Expr::BoolConst(false) => { /* caller should have pruned */ }
                Expr::And(xs) => { for x in xs { collect(x, pos, neg); } }
                Expr::Not(b) => {
                    if is_atomic(b) {
                        neg.insert(fingerprint_expr(b));
                    } else {
                        // Nested not of non-atomic: keep recursively, we might still see literals inside
                        collect(b, pos, neg);
                    }
                }
                x if is_atomic(x) => { pos.insert(fingerprint_expr(x)); }
                other => {
                    // Non-atomic non-not/non-and: treat as a single literal to be safe
                    // (keeps factoring conservative)
                    pos.insert(fingerprint_expr(other));
                }
            }
        }
        let mut p = HashSet::new();
        let mut n = HashSet::new();
        collect(g, &mut p, &mut n);
        (p, n)
    }

    #[inline]
    fn guard_has_literal(g: &Expr, key: u64, pol: Pol) -> bool {
        let (p, n) = guard_literals(g);
        match pol {
            Pol::Pos => p.contains(&key),
            Pol::Neg => n.contains(&key),
        }
    }

    #[inline]
    fn guards_contradict(a: &Expr, b: &Expr) -> bool {
        let (pa, na) = guard_literals(a);
        let (pb, nb) = guard_literals(b);
        // if a has X and b has ¬X (or vice versa), conjunction contradicts
        !pa.is_disjoint(&nb) || !pb.is_disjoint(&na)
    }

    // ---------- Everywhere ITE-lifting core ----------
    fn go(e: &Expr) -> Vec<(Expr, Expr)> {
        match e {
            // ---- ITE: hoist condition into guards, recursively eliminating nested ITEs in cond/branches ----
            Expr::Ite(c, t_e, f_e) => {
                let c_alts = go(c);
                let t_alts = go(t_e);
                let f_alts = go(f_e);

                let mut out = Vec::new();
                for (gc, ce) in c_alts {
                    // THEN branch under (gc ∧ ce)
                    for (gt, te) in &t_alts {
                        let g = and_guard(and_guard(gc.clone(), gt.clone()), ce.clone());
                        if !matches!(g, Expr::BoolConst(false)) {
                            out.push((g, te.clone()));
                        }
                    }
                    // ELSE branch under (gc ∧ ¬ce)
                    let not_ce = Expr::Not(Box::new(ce));
                    for (gf, fe) in &f_alts {
                        let g = and_guard(and_guard(gc.clone(), gf.clone()), not_ce.clone());
                        if !matches!(g, Expr::BoolConst(false)) {
                            out.push((g, fe.clone()));
                        }
                    }
                }
                out
            }

            // ---- Leaves: already ITE-free ----
            Expr::Sym(_) | Expr::BoolConst(_) | Expr::IntConst(_) | Expr::BVConst{..} => {
                vec![(t(), e.clone())]
            }

            // ---- Unary map ----
            Expr::Not(x)               => map_unary(go(x), |a| Expr::Not(Box::new(a))),
            Expr::BVNot(x)             => map_unary(go(x), |a| Expr::BVNot(Box::new(a))),
            Expr::BVNeg(x)             => map_unary(go(x), |a| Expr::BVNeg(Box::new(a))),
            Expr::ZeroExtend{k,e}      => map_unary(go(e), |a| Expr::ZeroExtend{ k:*k, e:Box::new(a) }),
            Expr::SignExtend{k,e}      => map_unary(go(e), |a| Expr::SignExtend{ k:*k, e:Box::new(a) }),
            Expr::Extract{hi,lo,e}     => map_unary(go(e), |a| Expr::Extract{ hi:*hi, lo:*lo, e:Box::new(a) }),

            // ---- Binary combine with factoring-aware product ----
            Expr::Eq(a,b)              => combine_bin(go(a), go(b), |x,y| Expr::Eq(Box::new(x),Box::new(y))),
            Expr::BVSub(a,b)           => combine_bin(go(a), go(b), |x,y| Expr::BVSub(Box::new(x),Box::new(y))),
            Expr::BVUDiv(a,b)          => combine_bin(go(a), go(b), |x,y| Expr::BVUDiv(Box::new(x),Box::new(y))),
            Expr::BVURem(a,b)          => combine_bin(go(a), go(b), |x,y| Expr::BVURem(Box::new(x),Box::new(y))),
            Expr::BVSDiv(a,b)          => combine_bin(go(a), go(b), |x,y| Expr::BVSDiv(Box::new(x),Box::new(y))),
            Expr::BVSRem(a,b)          => combine_bin(go(a), go(b), |x,y| Expr::BVSRem(Box::new(x),Box::new(y))),
            Expr::BVSMod(a,b)          => combine_bin(go(a), go(b), |x,y| Expr::BVSMod(Box::new(x),Box::new(y))),
            Expr::BVShl(a,b)           => combine_bin(go(a), go(b), |x,y| Expr::BVShl(Box::new(x),Box::new(y))),
            Expr::BVLshr(a,b)          => combine_bin(go(a), go(b), |x,y| Expr::BVLshr(Box::new(x),Box::new(y))),
            Expr::BVAshr(a,b)          => combine_bin(go(a), go(b), |x,y| Expr::BVAshr(Box::new(x),Box::new(y))),
            Expr::BVUlt(a,b)           => combine_bin(go(a), go(b), |x,y| Expr::BVUlt(Box::new(x),Box::new(y))),
            Expr::BVUle(a,b)           => combine_bin(go(a), go(b), |x,y| Expr::BVUle(Box::new(x),Box::new(y))),
            Expr::BVUgt(a,b)           => combine_bin(go(a), go(b), |x,y| Expr::BVUgt(Box::new(x),Box::new(y))),
            Expr::BVUge(a,b)           => combine_bin(go(a), go(b), |x,y| Expr::BVUge(Box::new(x),Box::new(y))),
            Expr::BVSlt(a,b)           => combine_bin(go(a), go(b), |x,y| Expr::BVSlt(Box::new(x),Box::new(y))),
            Expr::BVSle(a,b)           => combine_bin(go(a), go(b), |x,y| Expr::BVSle(Box::new(x),Box::new(y))),
            Expr::BVSgt(a,b)           => combine_bin(go(a), go(b), |x,y| Expr::BVSgt(Box::new(x),Box::new(y))),
            Expr::BVSge(a,b)           => combine_bin(go(a), go(b), |x,y| Expr::BVSge(Box::new(x),Box::new(y))),

            // ---- N-ary with guard factoring & left-to-right product ----
            Expr::And(xs)              => combine_n(xs, |ys| Expr::And(ys)),
            Expr::Or(xs)               => combine_n(xs, |ys| Expr::Or(ys)),
            Expr::Xor(xs)              => combine_n(xs, |ys| Expr::Xor(ys)),
            Expr::BVXor(xs)            => combine_n(xs, |ys| Expr::BVXor(ys)),
            Expr::BVAnd(xs)            => combine_n(xs, |ys| Expr::BVAnd(ys)),
            Expr::BVOr(xs)             => combine_n(xs, |ys| Expr::BVOr(ys)),
            Expr::BVAdd(xs)            => combine_n(xs, |ys| Expr::BVAdd(ys)),
            Expr::BVMul(xs)            => combine_n(xs, |ys| Expr::BVMul(ys)),
            Expr::Concat(xs)           => combine_n(xs, |ys| Expr::Concat(ys)),
            Expr::Distinct(xs)         => combine_n(xs, |ys| Expr::Distinct(ys)),

            // Helpers that survived inlining (shouldn’t): pass through; RHS is ITE-free already
            Expr::App(_, _)            => vec![(t(), e.clone())],
        }
    }

    // ---- unary/n-ary/binary helpers (with mitigations inside) ----

    fn map_unary(v: Vec<(Expr, Expr)>, build: impl Fn(Expr) -> Expr) -> Vec<(Expr, Expr)> {
        v.into_iter().map(|(g, e)| (g, build(e))).collect()
    }

    fn combine_bin(
        a: Vec<(Expr, Expr)>,
        b: Vec<(Expr, Expr)>,
        build: impl Fn(Expr, Expr) -> Expr,
    ) -> Vec<(Expr, Expr)> {
        // left-to-right with pruning and small cap
        let mut out = Vec::new();
        for (ga, ea) in a {
            for (gb, eb) in &b {
                if guards_contradict(&ga, gb) { continue; }
                let g = and_guard(ga.clone(), gb.clone());
                if !matches!(g, Expr::BoolConst(false)) {
                    out.push((g, build(ea.clone(), eb.clone())));
                    if out.len() > MAX_ROWS { return out; }
                }
            }
        }
        out
    }

    // Guard factoring over a vector of children (already ITE-lifted) with an n-ary builder.
    fn combine_n(
        xs: &[Expr],
        build: impl Fn(Vec<Expr>) -> Expr + Copy,
    ) -> Vec<(Expr, Expr)> {
        // Get alternatives per child
        let mut parts: Vec<Vec<(Expr, Expr)>> = Vec::with_capacity(xs.len());
        for x in xs {
            let alts = go(x);
            // skip singletons fast-path
            parts.push(alts);
        }

        // Try guard factoring on a common condition across children.
        if let Some((cond_key, cond_repr)) = choose_common_cond(&parts) {
            // Positive branch (cond), Negative branch (¬cond)
            let mut pos_parts = Vec::with_capacity(parts.len());
            let mut neg_parts = Vec::with_capacity(parts.len());

            for ch in &parts {
                // Filter per branch:
                //  - take those that explicitly mention the branch literal,
                //  - or those neutral to cond (mention neither), which we keep in both branches.
                let mut pos_vec = Vec::new();
                let mut neg_vec = Vec::new();
                for (g, e) in ch {
                    let has_pos = guard_has_literal(g, cond_key, Pol::Pos);
                    let has_neg = guard_has_literal(g, cond_key, Pol::Neg);
                    if has_pos { pos_vec.push((g.clone(), e.clone())); }
                    if has_neg { neg_vec.push((g.clone(), e.clone())); }
                    if !has_pos && !has_neg {
                        // neutral: allowed in both branches
                        pos_vec.push((g.clone(), e.clone()));
                        neg_vec.push((g.clone(), e.clone()));
                    }
                }
                // If a branch becomes empty, factoring is not helpful; abort factoring.
                if pos_vec.is_empty() || neg_vec.is_empty() {
                    return ltr_product(parts, build);
                }
                pos_parts.push(pos_vec);
                neg_parts.push(neg_vec);
            }

            // Build both branches left-to-right, then add the branch literal to the guard.
            let mut out = Vec::new();

            for (g, rhs) in ltr_product(pos_parts, build) {
                // add `cond_repr` to guard (even if some children already had it; harmless)
                let g2 = and_guard(g, cond_repr.clone());
                if !matches!(g2, Expr::BoolConst(false)) { out.push((g2, rhs)); }
                if out.len() > MAX_ROWS { return out; }
            }
            let not_cond = Expr::Not(Box::new(cond_repr));
            for (g, rhs) in ltr_product(neg_parts, build) {
                let g2 = and_guard(g, not_cond.clone());
                if !matches!(g2, Expr::BoolConst(false)) { out.push((g2, rhs)); }
                if out.len() > MAX_ROWS { return out; }
            }
            return out;
        }

        // Fallback: plain left-to-right product with pruning
        ltr_product(parts, build)
    }

    // Left-to-right row builder with early pruning and a soft cap
    fn ltr_product(
        parts: Vec<Vec<(Expr, Expr)>>,
        build: impl Fn(Vec<Expr>) -> Expr + Copy,
    ) -> Vec<(Expr, Expr)> {
        // Row = (guard, collected_child_exprs)
        let mut rows: Vec<(Expr, Vec<Expr>)> = vec![(Expr::BoolConst(true), Vec::new())];

        for ch in parts {
            if ch.len() == 1 {
                // singleton fast-path
                let (g1, e1) = &ch[0];
                let mut next = Vec::with_capacity(rows.len());
                for (gr, mut es) in rows {
                    if guards_contradict(&gr, g1) { continue; }
                    let g = and_guard(gr, g1.clone());
                    if !matches!(g, Expr::BoolConst(false)) {
                        es.push(e1.clone());
                        next.push((g, es));
                    }
                }
                rows = next;
            } else {
                // general combine
                let mut next = Vec::new();
                for (gr, es) in &rows {
                    for (g1, e1) in &ch {
                        if guards_contradict(gr, g1) { continue; }
                        let g = and_guard(gr.clone(), g1.clone());
                        if matches!(g, Expr::BoolConst(false)) { continue; }
                        let mut ys = es.clone();
                        ys.push(e1.clone());
                        next.push((g, ys));
                        if next.len() > MAX_ROWS { return materialize(next, build); }
                    }
                }
                rows = next;
                if rows.is_empty() { break; }
            }
        }
        materialize(rows, build)
    }

    #[inline]
    fn materialize(rows: Vec<(Expr, Vec<Expr>)>, build: impl Fn(Vec<Expr>) -> Expr + Copy)
        -> Vec<(Expr, Expr)>
    {
        rows.into_iter().map(|(g, ys)| (g, build(ys))).collect()
    }

    /// Pick a "best" common condition across children to factor on.
    /// We look for a literal L that appears (positively or negatively) in **multiple children**.
    fn choose_common_cond(parts: &[Vec<(Expr, Expr)>]) -> Option<(u64, Expr)> {
        // For each candidate fingerprint, count in how many children it appears at least once.
        // Also keep one representative Expr for pretty/guard insertion.
        let mut child_presence: HashMap<u64, usize> = HashMap::new();
        let mut any_repr: HashMap<u64, Expr> = HashMap::new();

        for ch in parts {
            let mut seen_in_child: HashSet<u64> = HashSet::new();
            for (g, _e) in ch {
                let (p, n) = guard_literals(g);
                for k in p.iter().chain(n.iter()) {
                    if seen_in_child.insert(*k) {
                        *child_presence.entry(*k).or_insert(0) += 1;
                        if !any_repr.contains_key(k) {
                            // Try to find a positive representative literal for readability; fallback to first thing we see.
                            // Here we can't recover the *exact* literal Expr from the set, so we re-scan once to find one.
                            any_repr.insert(*k, pick_literal_expr(g, *k).unwrap_or_else(|| Expr::Sym(format!("lit_{}", k))));
                        }
                    }
                }
            }
        }

        // Choose the candidate seen in the most children (>= 2)
        let (best_key, best_count) = child_presence
        .iter()
        .max_by_key(|(_, c)| *c)    // c: &usize -> compare by value
        .map(|(k, c)| (*k, *c))?;   // copy out (&u64, &usize) -> (u64, usize)

        if best_count < 2 { return None; }

        // Representative literal to conjoin in branches; if it was negative in the only occurrence,
        // we still return the base (positive) form and layer polarity in the branch.
        let rep = any_repr.get(&best_key)?.clone();
        Some((best_key, rep))
    }

    // Try to extract a concrete literal Expr with the given fingerprint from guard `g`.
    fn pick_literal_expr(g: &Expr, key: u64) -> Option<Expr> {
        match g {
            Expr::And(xs) => {
                for x in xs {
                    if let Some(e) = pick_literal_expr(x, key) { return Some(e); }
                }
                None
            }
            Expr::Not(b) if fingerprint_expr(b) == key => Some((**b).clone()),
            other if fingerprint_expr(other) == key => Some(other.clone()),
            _ => None,
        }
    }

    go(e)
}
