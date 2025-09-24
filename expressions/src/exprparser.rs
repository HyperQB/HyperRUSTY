use pest::Parser;
use pest::iterators::Pair;
use pest_derive::Parser;
use std::collections::HashMap;
use crate::TrajQuant;
use crate::Expression::*;
use crate::expression_to_string;
use std::collections::HashSet;
use crate::exprparser::Rule as PRule;
use regex::Regex;
// use crate::{Expression, Literal};        // enums you defined
// use crate::quant::Quant;                 // Quant::{Forall, Exists}

// ---- Your existing ASTs (adjust imports/types to your project) ----
use crate::{Expression, Literal as Lit, Quant};
use crate::Literal::*;
type Variable = String;                         // adjust if you use a dedicated type

// ---- Result object you likely want to return ----
pub struct HyperParsed {
    pub prefix: Vec<(Quant, String)>,   // from Forall/Exists … .
    pub formula: Expression,                   // inner_hltl or inner_altl
}

pub struct AHLTLParsed {
    pub prefix: Vec<(Quant, String)>,   // from Forall/Exists … .
    pub trajs: Vec<(TrajQuant, String)>,   // from A/E … .
    pub pos_prefix: Vec<(Quant, String)>,
    pub ahltl_expr: Expression, 
    // pub pos_prefix: Vec<(Quant, String)>,                  // inner_hltl or inner_altl
}

#[derive(Parser)]
#[grammar = "hyperltl.pest"]  // put the grammar text below into this file
struct HyperParser;

pub fn parse_hyperltl(
    input: &str,
    max_bit_map: &HashMap<String, usize>,
) -> Result<HyperParsed, String> {
    let mut pairs = HyperParser::parse(Rule::formula, input).map_err(|e| e.to_string())?;
    let root = pairs.next().unwrap();
    let pf = root.into_inner().next().unwrap();
    let (tail, prefix) = collect_prefix(pf)?;
    let formula = parse_form_rec(tail)?;
    // println!("To be parsed: {:?}", formula);
    // Rewrite equalities that involve bit-blasted variables
    let formula = bitblast_eqs(&formula, max_bit_map);

    Ok(HyperParsed { prefix, formula })
}

pub fn parse_ahltl(
    input: &str,
    max_bit_map: &HashMap<String, usize>,
    bound: usize,
) -> Result<AHLTLParsed, String> {
    // Parse the input into a Pest tree
    let mut pairs = HyperParser::parse(Rule::formula, input).map_err(|e| e.to_string())?;
    let root = pairs.next().ok_or("empty parse tree")?;
    let pf   = root.clone().into_inner().next().ok_or("empty formula body")?;

    // 1) Path prefix: Forall/Exists
    let (after_paths, prefix) = collect_prefix(pf)?;

    // 2) Trajectory quantifiers: A/E t .
    let trajs: Vec<(TrajQuant, String)> = extract_traj_quants(&root);

    // 3) Parse the remaining body (ALT(L) or HLTL depending on your grammar)
    let inner_formula = parse_form_rec(after_paths)?;
    let inner_formula = bitblast_eqs(&inner_formula, max_bit_map);

    println!("\nPath Prefix: {:?} ", prefix);
    println!("\nTrajectories: {:?}", trajs);
    println!("\nInner: {:?}", inner_formula);

    // 4) Build the AHLTL encoding (parameterize k as needed)
    let k = 3;
    let (ahltl_expr, pos_prefix) = build_ahltl_with_selectors(&prefix, &trajs, &inner_formula, bound);
    println!("\nPositions:  {:?}", pos_prefix);
    // println!("\nConstraints: {:?}", expression_to_string(&ahltl_expr));


    // 5) Rewrite equalities (bit-blast against max_bit_map)
    // let final_formula = bitblast_eqs(&phi_ahltl, max_bit_map);



    Ok(AHLTLParsed { prefix, trajs, pos_prefix, ahltl_expr})

}



fn big_or(mut xs: Vec<Expression>) -> Expression {
    match xs.len() {
        0 => Expression::False,
        1 => xs.pop().unwrap(),
        _ => Expression::MOr(xs.into_iter().map(Box::new).collect()),
    }
}
fn big_and(mut xs: Vec<Expression>) -> Expression {
    match xs.len() {
        0 => Expression::True,
        1 => xs.pop().unwrap(),
        _ => Expression::MAnd(xs.into_iter().map(Box::new).collect()),
    }
}

fn lit_atom<S: Into<String>>(s: S) -> Expression {
    Expression::Literal(Lit::Atom(s.into()))
}
fn lit_neg_atom<S: Into<String>>(s: S) -> Expression {
    Expression::Literal(Lit::NegAtom(s.into()))
}

/// selector name s_<PATH>_<i>
fn sel_name(path: &str, i: usize) -> String {
    format!("t_{}_{}", path, i)
}

/// p[PATH][i]
fn atom_at(base: &str, path: &str, i: usize) -> Expression {
    lit_atom(format!("{base}[{path}][{i}]"))
}
fn neg_atom_at(base: &str, path: &str, i: usize) -> Expression {
    lit_neg_atom(format!("{base}[{path}][{i}]"))
}

/// (s_path_i <-> p[path][i])  (or <-> ¬p[path][i] if `neg`)
fn lane_iff(base: &str, path: &str, i: usize, neg: bool) -> Expression {
    let s   = lit_atom(sel_name(path, i));
    let ap  = if neg { neg_atom_at(base, path, i) } else { atom_at(base, path, i) };
    Expression::Iff(Box::new(s), Box::new(ap))
}

/// Very small parser for variables like `NAME[PATH][TIME]`
/// Returns (base, path, time) if it matches exactly that shape.
fn parse_base_path_time(v: &str) -> Option<(String, String, String)> {
    // matches:  line[A][t],  line [ A ] [ t2 ],  foo.bar[B][0], etc.
    static ONCE: std::sync::Once = std::sync::Once::new();
    static mut RE: Option<Regex> = None;
    ONCE.call_once(|| {
        let re = Regex::new(
            r"^\s*([^\[\]\s]+)\s*\[\s*([^\[\]\s]+)\s*\]\s*\[\s*([^\[\]\s]+)\s*\]\s*$"
        ).expect("regex");
        unsafe { RE = Some(re); }
    });
    let re = unsafe { RE.as_ref().unwrap() };
    let caps = re.captures(v)?;
    Some((
        caps.get(1)?.as_str().to_string(), // base
        caps.get(2)?.as_str().to_string(), // path
        caps.get(3)?.as_str().to_string(), // time
    ))
}

fn selector_iff_or(base: &str, path: &str, k: usize) -> Expression {
    let lanes = (0..=k).map(|i| {
        let sel  = format!("t_{}_{}", path, i);
        let atom = format!("{base}[{path}][{i}]");
        Box::new(Expression::Iff(
            Box::new(Expression::Literal(Lit::Atom(sel))),
            Box::new(Expression::Literal(Lit::Atom(atom))),
        ))
    }).collect::<Vec<_>>();
    Expression::MOr(lanes)
}

fn rewrite_for_traj(
    e: &Expression,
    traj_name: &str,
    path_names: &[&str],
    k: usize,
) -> Expression {
    use Expression::*;
    match e {
        Literal(Lit::Atom(v)) => {
            if let Some((base, path, time)) = parse_base_path_time(v) {
                if time == traj_name && path_names.iter().any(|p| *p == path) {
                    // ∨_i (s_path_i <-> base[path][i])
                    return selector_iff_or(&base, &path, k);
                }
            }
            e.clone()
        }
        Literal(Lit::NegAtom(v)) => {
            if let Some((base, path, time)) = parse_base_path_time(v) {
                if time == traj_name && path_names.iter().any(|p| *p == path) {
                    // ¬(∨_i (s_path_i <-> base[path][i]))
                    return Expression::Neg(Box::new(selector_iff_or(&base, &path, k)));
                }
            }
            e.clone()
        }
        Neg(x)       => Neg(Box::new(rewrite_for_traj(x, traj_name, path_names, k))),
        G(x)         => G(Box::new(rewrite_for_traj(x, traj_name, path_names, k))),
        F(x)         => F(Box::new(rewrite_for_traj(x, traj_name, path_names, k))),
        X(x)         => X(Box::new(rewrite_for_traj(x, traj_name, path_names, k))),
        And(a,b)     => And(
            Box::new(rewrite_for_traj(a, traj_name, path_names, k)),
            Box::new(rewrite_for_traj(b, traj_name, path_names, k))),
        Or(a,b)      => Or(
            Box::new(rewrite_for_traj(a, traj_name, path_names, k)),
            Box::new(rewrite_for_traj(b, traj_name, path_names, k))),
        Implies(a,b) => Implies(
            Box::new(rewrite_for_traj(a, traj_name, path_names, k)),
            Box::new(rewrite_for_traj(b, traj_name, path_names, k))),
        Iff(a,b)     => Iff(
            Box::new(rewrite_for_traj(a, traj_name, path_names, k)),
            Box::new(rewrite_for_traj(b, traj_name, path_names, k))),
        U(a,b)       => U(
            Box::new(rewrite_for_traj(a, traj_name, path_names, k)),
            Box::new(rewrite_for_traj(b, traj_name, path_names, k))),
        R(a,b)       => R(
            Box::new(rewrite_for_traj(a, traj_name, path_names, k)),
            Box::new(rewrite_for_traj(b, traj_name, path_names, k))),
        MAnd(xs)     => MAnd(xs.iter().map(|x| Box::new(rewrite_for_traj(x, traj_name, path_names, k))).collect()),
        MOr(xs)      => MOr(xs.iter().map(|x| Box::new(rewrite_for_traj(x, traj_name, path_names, k))).collect()),
        True | False => e.clone(),
    }
}

/// Drop all temporal operators after trajectory rewriting.
/// NOTE:
/// - For G/F/X we just return the (recursively stripped) body.
/// - For U/R we provide *very conservative, not semantically exact* fallbacks:
///     U(a,b) -> (a ∧ b) ∨ b   (i.e., imply-at-least-b)
///     R(a,b) -> b ∨ a         (very weak; adjust if you really need U/R here)
fn strip_temporal(e: &Expression) -> Expression {
    use Expression::*;
    match e {
        True | False | Literal(_) => e.clone(),

        Neg(x)   => Neg(Box::new(strip_temporal(x))),
        And(a,b) => And(Box::new(strip_temporal(a)), Box::new(strip_temporal(b))),
        Or(a,b)  => Or(Box::new(strip_temporal(a)),  Box::new(strip_temporal(b))),
        Iff(a,b) => Iff(Box::new(strip_temporal(a)), Box::new(strip_temporal(b))),
        Implies(a,b) => Implies(Box::new(strip_temporal(a)), Box::new(strip_temporal(b))),
        MAnd(xs) => MAnd(xs.iter().map(|x| Box::new(strip_temporal(x))).collect()),
        MOr(xs)  => MOr(xs.iter().map(|x| Box::new(strip_temporal(x))).collect()),

        // Erase single-operand temporals (selectors already encode time choice)
        G(x) | F(x) | X(x) => strip_temporal(x),

        // Fallbacks for U/R — adjust/replace with your bounded-unroll if needed.
        U(a,b) => {
            let aa = strip_temporal(a);
            let bb = strip_temporal(b);
            Or(Box::new(And(Box::new(aa), Box::new(bb.clone()))), Box::new(bb))
        }
        R(a,b) => {
            let aa = strip_temporal(a);
            let bb = strip_temporal(b);
            Or(Box::new(bb), Box::new(aa))
        }
    }
}

/// Build the selector-encoded AHLTL body and extend the prefix with ∃-selectors.
/// After rewriting, **strip all temporal operators** to keep it propositional.
pub fn build_ahltl_with_selectors(
    paths: &[(Quant, String)],
    trajs: &[(TrajQuant, String)],
    inner: &Expression,
    k: usize,
) -> (Expression, Vec<(Quant, String)>) {
    // unique path names from the prefix
    let mut seen = HashSet::new();
    let path_names: Vec<String> = paths.iter()
        .map(|(_, p)| p.clone())
        .filter(|p| seen.insert(p.clone()))
        .collect();
    let path_slices: Vec<&str> = path_names.iter().map(|s| s.as_str()).collect();

    // rewrite for each trajectory variable
    let mut rewritten = inner.clone();
    for (_tq, tname) in trajs {
        rewritten = rewrite_for_traj(&rewritten, tname, &path_slices, k);
    }

    // NOW: remove any remaining temporals (F/G/X/U/R)
    let rewritten_no_temporal = strip_temporal(&rewritten);

    // extend prefix with ∃ selectors
    let mut prefix_ext: Vec<(Quant, String)> = Vec::new();
    for path in &path_names {
        for i in 0..=k {
            prefix_ext.push((Quant::Exists, format!("t_{}_{}", path, i)));
        }
    }

    (rewritten_no_temporal, prefix_ext)
}

/// Rewrites any literal whose time = `traj_var` into a selector-gated disjunction
/// using selectors for the corresponding path.
/// - `paths` tells us which path symbols get selectors (e.g., &["A","B"]).
/// - `traj_var` is the trajectory variable name (e.g., "t").
/// - `k` is the bound; indices are 0..=k.
/// Returns the rewritten Expression and the list of selector variable names you must quantify under ∃.
pub fn selectify_wrt_trajectories(
    e: &Expression,
    paths: &[&str],
    traj_var: &str,
    k: usize,
    out_exist_selectors: &mut Vec<String>,
) -> Expression {
    // Precompute selector names and remember them for quantification
    let mut path_to_selectors: HashMap<String, Vec<String>> = HashMap::new();
    for &p in paths {
        let mut sels = Vec::with_capacity(k + 1);
        for i in 0..=k {
            let s = sel_name(p, i);
            sels.push(s.clone());
            out_exist_selectors.push(s);
        }
        path_to_selectors.insert(p.to_string(), sels);
    }

    fn go(
        e: &Expression,
        traj_var: &str,
        k: usize,
        path_to_selectors: &HashMap<String, Vec<String>>,
    ) -> Expression {
        use Expression::*;
        match e {
            // Atom / NegAtom cases: check if it is NAME[PATH][traj_var]
            Expression::Literal(Lit::Atom(v)) => {
                if let Some((base, path, time)) = parse_base_path_time(v) {
                    if time == traj_var {
                        if let Some(_selset) = path_to_selectors.get(&path) {
                            // ∨_i (s_path_i <-> base[path][i])
                            let lanes = (0..=k).map(|i| lane_iff(&base, &path, i, false)).collect();
                            return big_or(lanes);
                        }
                    }
                }
                // otherwise keep as is
                e.clone()
            }
            Expression::Literal(Lit::NegAtom(v)) => {
                if let Some((base, path, time)) = parse_base_path_time(v) {
                    if time == traj_var {
                        if let Some(_selset) = path_to_selectors.get(&path) {
                            // ∨_i (s_path_i <-> ¬base[path][i])
                            let lanes = (0..=k).map(|i| lane_iff(&base, &path, i, true)).collect();
                            return big_or(lanes);
                        }
                    }
                }
                e.clone()
            }

            // Structural recursion
            Neg(x) => Neg(Box::new(go(x, traj_var, k, path_to_selectors))),
            And(a,b) => And(
                Box::new(go(a, traj_var, k, path_to_selectors)),
                Box::new(go(b, traj_var, k, path_to_selectors)),
            ),
            Or(a,b) => Or(
                Box::new(go(a, traj_var, k, path_to_selectors)),
                Box::new(go(b, traj_var, k, path_to_selectors)),
            ),
            Iff(a,b) => Iff(
                Box::new(go(a, traj_var, k, path_to_selectors)),
                Box::new(go(b, traj_var, k, path_to_selectors)),
            ),
            Implies(a,b) => Implies(
                Box::new(go(a, traj_var, k, path_to_selectors)),
                Box::new(go(b, traj_var, k, path_to_selectors)),
            ),
            MAnd(xs) => MAnd(xs.iter().map(|x| Box::new(go(x, traj_var, k, path_to_selectors))).collect()),
            MOr(xs)  => MOr(xs.iter().map(|x| Box::new(go(x, traj_var, k, path_to_selectors))).collect()),

            // If you keep temporal nodes in this representation, recurse into them too:
            G(x) => G(Box::new(go(x, traj_var, k, path_to_selectors))),
            F(x) => F(Box::new(go(x, traj_var, k, path_to_selectors))),
            X(x) => X(Box::new(go(x, traj_var, k, path_to_selectors))),
            U(a,b)=> U(Box::new(go(a, traj_var, k, path_to_selectors)),
                       Box::new(go(b, traj_var, k, path_to_selectors))),
            R(a,b)=> R(Box::new(go(a, traj_var, k, path_to_selectors)),
                       Box::new(go(b, traj_var, k, path_to_selectors))),

            True | False => e.clone(),
        }
    }

    go(e, traj_var, k, &path_to_selectors)
}



















/// Collect trajectory quantifiers of the form `A t .` or `E t .`
/// Walks the subtree and returns a vector of `(TrajQuant, ident)`.
pub fn extract_traj_quants(root: &Pair<Rule>) -> Vec<(TrajQuant, String)> {
    let mut out = Vec::new();
    walk_trajs(root, &mut out);
    out
}

fn walk_trajs(node: &Pair<Rule>, out: &mut Vec<(TrajQuant, String)>) {
    match node.as_rule() {
        Rule::traj_formula => {
            // Infer A/E from the start of the matched text.
            let span = node.as_str().trim_start();
            let tq = match span.chars().next() {
                Some('A') => TrajQuant::TrajA,
                Some('E') => TrajQuant::TrajE,
                _ => {
                    // If your grammar exposes a dedicated tquant child, you can read that instead.
                    // Fall through to recurse anyway.
                    for ch in node.clone().into_inner() {
                        walk_trajs(&ch, out);
                    }
                    return;
                }
            };

            // Find the first ident child inside this traj_formula.
            let mut ident_name: Option<String> = None;
            for ch in node.clone().into_inner() {
                if ch.as_rule() == Rule::ident {
                    ident_name = Some(ch.as_str().to_string());
                    break;
                }
            }
            if let Some(name) = ident_name {
                out.push((tq, name));
            }

            // Recurse into ALL children to catch nested traj_formula’s.
            for ch in node.clone().into_inner() {
                walk_trajs(&ch, out);
            }
        }

        // Generic recursion: keep scanning the tree for more traj_formula nodes.
        _ => {
            for ch in node.clone().into_inner() {
                walk_trajs(&ch, out);
            }
        }
    }
}

/// Recursively rewrite `=` (Iff) between atoms whose base appears in `max_bit_map`.
fn bitblast_eqs(expr: &Expression, max_bit_map: &HashMap<String, usize>) -> Expression {
    use Expression::*;

    match expr {
        // Recurse
        Neg(x)       => Neg(Box::new(bitblast_eqs(x, max_bit_map))),
        And(a,b)     => And(Box::new(bitblast_eqs(a, max_bit_map)), Box::new(bitblast_eqs(b, max_bit_map))),
        Or(a,b)      => Or(Box::new(bitblast_eqs(a, max_bit_map)), Box::new(bitblast_eqs(b, max_bit_map))),
        Implies(a,b) => Implies(Box::new(bitblast_eqs(a, max_bit_map)), Box::new(bitblast_eqs(b, max_bit_map))),

        // ===== FIXED: handle atom==atom, atom==int, int==atom =====
        Iff(a, b) => {
            let lhs_atom = parse_atom_name(a.as_ref());
            let rhs_atom = parse_atom_name(b.as_ref());
            let lhs_int  = parse_int_literal(a.as_ref());
            let rhs_int  = parse_int_literal(b.as_ref());

            // atom == atom (same base, listed in map) → bitwise equivalence per lane
            if let (Some(lhs), Some(rhs)) = (lhs_atom.clone(), rhs_atom.clone()) {
                // if lhs.base == rhs.base {
                    if let Some(&bw) = max_bit_map.get(&lhs.base) {
                        return bitblast_atom_eq(&lhs, &rhs, bw);
                    }
                // }
            }

            // atom == integer constant
            if let (Some(lhs), Some(c)) = (lhs_atom.clone(), rhs_int) {
                if let Some(&bw) = max_bit_map.get(&lhs.base) {
                    return bitblast_atom_eq_const(&lhs, c, bw);
                }
            }

            // integer constant == atom
            if let (Some(c), Some(rhs)) = (lhs_int, rhs_atom.clone()) {
                if let Some(&bw) = max_bit_map.get(&rhs.base) {
                    return bitblast_atom_eq_const(&rhs, c, bw);
                }
            }

            // otherwise recurse normally
            Iff(
                Box::new(bitblast_eqs(a, max_bit_map)),
                Box::new(bitblast_eqs(b, max_bit_map))
            )
        }

        MAnd(xs) => MAnd(xs.iter().map(|x| Box::new(bitblast_eqs(x, max_bit_map))).collect()),
        MOr(xs)  => MOr(xs.iter().map(|x| Box::new(bitblast_eqs(x, max_bit_map))).collect()),
        G(x) | F(x) | X(x) => {
            let inner = bitblast_eqs(x, max_bit_map);
            match expr { 
                G(_) => G(Box::new(inner)),
                F(_) => F(Box::new(inner)),
                _    => X(Box::new(inner)),
            }
        }
        U(a,b) | R(a,b) => {
            let la = bitblast_eqs(a, max_bit_map);
            let rb = bitblast_eqs(b, max_bit_map);
            match expr {
                U(_,_) => U(Box::new(la), Box::new(rb)),
                _      => R(Box::new(la), Box::new(rb)),
            }
        }

        // Leaves unchanged
        True | False | Literal(_) => expr.clone(),
    }
}

/// If `e` is an integer literal atom (e.g., "0", "1", "42", "-3"), return its value.
fn parse_int_literal(e: &Expression) -> Option<i64> {
    match e {
        Expression::Literal(Lit::Atom(s)) |
        Expression::Literal(Lit::NegAtom(s)) => s.parse::<i64>().ok(),
        _ => None,
    }
}

/// Build (BASE_{bw-1}[p][t] &/¬ ...) ∧ ... ∧ (BASE_0[p][t] &/¬ ...) for `atom == const`
fn bitblast_atom_eq_const(lhs: &AtomParts, val: i64, bitwidth: usize) -> Expression {
    // (optional) sanity check two's-complement fit
    let needed_bits = if val >= 0 {
        64 - val.leading_zeros()
    } else {
        64 - (!val).leading_zeros() + 1
    } as usize;
    if needed_bits > bitwidth {
        eprintln!(
            "Error: bitwidth {} too small to represent {} for {}",
            bitwidth, val, lhs.base
        );
        std::process::exit(1);
    }

    let mut lanes = Vec::with_capacity(bitwidth);
    // MSB..LSB for readability (e.g., PC_2, PC_1, PC_0)
    for i in (0..bitwidth).rev() {
        let expected = (val >> i) & 1;
        let name = bit_name(lhs, i); // you already have this helper
        let bit  = Expression::Literal(Lit::Atom(name));
        let lane = if expected == 1 {
            bit
        } else {
            Expression::Neg(Box::new(bit))
        };
        lanes.push(Box::new(lane));
    }
    Expression::MAnd(lanes)
}

fn bit_name(atom: &AtomParts, i: usize) -> String {
    let mut s = format!("{}_{}", atom.base, i);   // e.g., "PC_2"
    s.push('[');
    s.push_str(&atom.path);                      // path is a String, not Option
    s.push(']');
    if let Some(t) = &atom.time {
        s.push('[');
        s.push_str(t);
        s.push(']');
    }
    s
}


#[derive(Clone, Debug)]
struct AtomParts {
    base: String,
    path: String,
    time: Option<String>,
}

/// If `e` is an atom or neg-atom, parse its name into parts.
fn parse_atom_name(e: &Expression) -> Option<AtomParts> {
    // 1) Get a &str for the atom text (handles Atom and NegAtom)
    let s: &str = match e {
        Expression::Literal(Lit::Atom(v))    => v.as_str(),
        Expression::Literal(Lit::NegAtom(v)) => v.as_str(),
        _ => return None,
    };

    // 2) Expect BASE[PATH] or BASE[PATH][TIME]
    let bytes = s.as_bytes();

    // find first '['
    let mut i = 0usize;
    while i < bytes.len() && bytes[i] != b'[' { i += 1; }
    if i == bytes.len() { return None; }
    let base = &s[..i];

    // find matching ']' for PATH
    let mut j = i + 1;
    while j < bytes.len() && bytes[j] != b']' { j += 1; }
    if j >= bytes.len() { return None; }
    let path = &s[i + 1..j];

    // optional [TIME]
    let mut time = None;
    if j + 1 < bytes.len() && bytes[j + 1] == b'[' {
        let mut k = j + 2;
        while k < bytes.len() && bytes[k] != b']' { k += 1; }
        if k >= bytes.len() { return None; }
        time = Some(s[j + 2..k].to_string());
    }

    Some(AtomParts {
        base: base.to_string(),
        path: path.to_string(),
        time,
    })
}


fn bit_atom(parts: &AtomParts, bit: usize) -> Expression {
    let mut name = format!("{}_{}", parts.base, bit);
    name.push('[');
    name.push_str(&parts.path);
    name.push(']');
    if let Some(t) = &parts.time {
        name.push('[');
        name.push_str(t);
        name.push(']');
    }
    Expression::Literal(Lit::Atom(name))
}

fn bitblast_atom_eq(lhs: &AtomParts, rhs: &AtomParts, bitwidth: usize) -> Expression {
    let mut lanes = Vec::with_capacity(bitwidth);
    // MSB..LSB for readability
    for i in (0..bitwidth).rev() {
        let a = bit_atom(lhs, i);
        let b = bit_atom(rhs, i);
        lanes.push(Box::new(Expression::Iff(Box::new(a), Box::new(b))));
    }
    Expression::MAnd(lanes)
}

// ------- prefix and formula descent -------

fn collect_prefix(p: Pair<Rule>) -> Result<(Pair<Rule>, Vec<(Quant, String)>), String> {
    let mut acc: Vec<(Quant, String)> = Vec::new();
    let mut cur = p;

    loop {
        // Dive through form_rec shells until we reach the next real node
        while cur.as_rule() == Rule::form_rec {
            let mut it = cur.clone().into_inner();
            cur = it.next().unwrap(); // path_formula | traj_formula | inner_hltl
        }

        if cur.as_rule() != Rule::path_formula {
            // We've reached traj_formula or inner_hltl; done collecting
            return Ok((cur, acc));
        }

        // cur: path_formula = quant ~ ident ~ "." ~ form_rec
        let mut it = cur.into_inner();
        let q_tok = it.next().unwrap(); // quant
        let ident = it.next().unwrap(); // ident
        let next  = it.next().unwrap(); // form_rec

        let q = match q_tok.as_str() {
            "Forall" => Quant::Forall,
            "Exists" => Quant::Exists,
            s => return Err(format!("unknown quantifier {s}")),
        };

        acc.push((q, ident.as_str().to_string()));
        cur = next; // continue with the remainder
    }
}

// Peel only the ALT(L) shell
fn is_altl_shell(rule: Rule) -> bool {
    matches!(rule, Rule::ahltl_form_rec)
}



/// Collect a sequence of trajectory quantifiers `A t .` / `E t .`
/// Returns (tail, traj_prefix)
pub fn collect_traj_prefix_only(
    mut cur: Pair<Rule>,
) -> Result<(Pair<Rule>, Vec<(TrajQuant, String)>), String> {
    let mut traj_acc: Vec<(TrajQuant, String)> = Vec::new();

    loop {
        while is_altl_shell(cur.as_rule()) {
            let mut it = cur.clone().into_inner();
            cur = it.next().ok_or("collect_traj_prefix_only: empty ahltl_form_rec")?;
        }

        if cur.as_rule() != Rule::traj_formula {
            return Ok((cur, traj_acc));
        }

        // Infer A/E from span (or read a dedicated token if your grammar has it)
        let span = cur.as_str().trim_start();
        let tq = if span.starts_with('A') {
            TrajQuant::TrajA
        } else if span.starts_with('E') {
            TrajQuant::TrajE
        } else {
            return Err(format!("traj_formula: cannot infer A/E in '{span}'"));
        };

        let mut it = cur.into_inner();
        let ident = it.next().ok_or("traj_formula: missing ident")?;
        let next  = it.next().ok_or("traj_formula: missing body (ahltl_form_rec)")?;

        traj_acc.push((tq, ident.as_str().to_string()));
        cur = next;
    }
}


fn parse_form_rec(p: Pair<Rule>) -> Result<Expression, String> {
    match p.as_rule() {
        Rule::form_rec => {
            // form_rec = { path_formula | traj_formula | inner_hltl }
            let mut it = p.into_inner();
            let next = it.next().unwrap();
            match next.as_rule() {
                Rule::path_formula => {
                    // Nested path quantifier: collect and parse recursively
                    let (inner_tail, mut more_prefix) = collect_prefix(next)?;
                    // We ignore extra nested prefix here; if you want to merge prefixes, do it.
                    let e = parse_form_rec(inner_tail)?;
                    // If you want to expose nested prefixes, change the return type.
                    Ok(e)
                }
                Rule::traj_formula => parse_traj_formula(next),
                Rule::inner_hltl   => parse_inner_hltl(next),
                _ => Err("unexpected form_rec content".into()),
            }
        }
        Rule::inner_hltl   => parse_inner_hltl(p),
        Rule::traj_formula => parse_traj_formula(p),
        r => Err(format!("unexpected rule in parse_form_rec: {:?}", r)),
    }
}

// ---- Trajectory layer (A/E) → produce Expression too (you can specialize) ----
fn parse_traj_formula(p: Pair<Rule>) -> Result<Expression, String> {
    // traj_formula = { ("A" | "E") ~ ident ~ "." ~ ahltl_form_rec }
    let mut it = p.into_inner();
    let quant_tok = it.next().unwrap(); // A or E
    let model_id  = it.next().unwrap(); // ident
    let tail      = it.next().unwrap(); // ahltl_form_rec

    // For now, we just parse the ALT LTL inside and ignore the model binding here
    // because your stamping later will append [model] anyway.
    let inner = parse_ahltl_form_rec(tail)?;
    let q = quant_tok.as_str();
    // If you want to keep A/E as part of AST, you could wrap with a marker.
    // For now we just return the inner expression.
    Ok(inner)
}

fn parse_ahltl_form_rec(p: Pair<Rule>) -> Result<Expression, String> {
    // ahltl_form_rec = { traj_formula | inner_altl }
    let mut it = p.into_inner();
    let next = it.next().unwrap();
    match next.as_rule() {
        Rule::traj_formula => parse_traj_formula(next),
        Rule::inner_altl   => parse_inner_altl(next),
        _ => Err("unexpected ahltl_form_rec content".into()),
    }
}

// ---- Inner HLTL: precedence chain ( = , -> , | , & , U , R , unary ) ----
fn parse_inner_hltl(p: Pair<Rule>) -> Result<Expression, String> {
    let eq = p.into_inner().next().unwrap(); // hequal
    parse_hequal(eq)
}
fn parse_inner_altl(p: Pair<Rule>) -> Result<Expression, String> {
    let eq = p.into_inner().next().unwrap(); // aequal
    parse_aequal(eq)
}

// === HLTL chain ===
fn parse_hequal(p: Pair<Rule>) -> Result<Expression, String> {
    // hequal = { himpl ~ ("=" ~ hequal)? }  '＝' means IFF
    let mut it = p.into_inner();
    let left = parse_himpl(it.next().unwrap())?;
    if let Some(eq_tail) = it.next() {
        let right = parse_hequal(eq_tail)?;
        Ok(Expression::Iff(Box::new(left), Box::new(right)))
    } else {
        Ok(left)
    }
}
fn parse_himpl(p: Pair<Rule>) -> Result<Expression, String> {
    // himpl = { hdisj ~ ("->" ~ himpl)? }
    let mut it = p.into_inner();
    let left = parse_hdisj(it.next().unwrap())?;
    if let Some(next) = it.next() {
        let right = parse_himpl(next)?;
        Ok(Expression::Implies(Box::new(left), Box::new(right)))
    } else { Ok(left) }
}
fn parse_hdisj(p: Pair<Rule>) -> Result<Expression, String> {
    // hdisj = { hconj ~ ("|" ~ hdisj)? }
    let mut it = p.into_inner();
    let left = parse_hconj(it.next().unwrap())?;
    if let Some(next) = it.next() {
        let right = parse_hdisj(next)?;
        Ok(Expression::Or(Box::new(left), Box::new(right)))
    } else { Ok(left) }
}
fn parse_hconj(p: Pair<Rule>) -> Result<Expression, String> {
    // hconj = { huntl ~ ("&" ~ hconj)? }
    let mut it = p.into_inner();
    let left = parse_huntl(it.next().unwrap())?;
    if let Some(next) = it.next() {
        let right = parse_hconj(next)?;
        Ok(Expression::And(Box::new(left), Box::new(right)))
    } else { Ok(left) }
}
fn parse_huntl(p: Pair<Rule>) -> Result<Expression, String> {
    // huntl = { hrels ~ ("U" ~ huntl)? }
    let mut it = p.into_inner();
    let left = parse_hrels(it.next().unwrap())?;
    if let Some(next) = it.next() {
        let right = parse_huntl(next)?;
        Ok(Expression::U(Box::new(left), Box::new(right)))
    } else { Ok(left) }
}
fn parse_hrels(p: Pair<Rule>) -> Result<Expression, String> {
    // hrels = { hfactor ~ ("R" ~ hrels)? }
    let mut it = p.into_inner();
    let left = parse_hfactor(it.next().unwrap())?;
    if let Some(next) = it.next() {
        let right = parse_hrels(next)?;
        Ok(Expression::R(Box::new(left), Box::new(right)))
    } else { Ok(left) }
}
fn parse_hfactor(p: Pair<Rule>) -> Result<Expression, String> {
    // hfactor = { unop ~ hfactor | "(" ~ inner_hltl ~ ")" | hltl_atom }
    match p.as_rule() {
        Rule::hfactor => {
            let mut it = p.into_inner();
            let first = it.next().unwrap();
            match first.as_rule() {
                Rule::unop => {
                    let op = first.as_str();
                    let rhs = parse_hfactor(it.next().unwrap())?;
                    Ok(match op {
                        "G" => Expression::G(Box::new(rhs)),
                        "F" => Expression::F(Box::new(rhs)),
                        "X" => Expression::X(Box::new(rhs)),
                        "~" => Expression::Neg(Box::new(rhs)),
                        _   => return Err(format!("unknown unop {op}")),
                    })
                }
                Rule::inner_hltl => parse_inner_hltl(first),
                Rule::hltl_atom  => parse_hltl_atom(first),
                _ => Err("bad hfactor".into()),
            }
        }
        _ => Err("expected hfactor".into()),
    }
}
fn parse_hltl_atom(p: Pair<Rule>) -> Result<Expression, String> {
    // hltl_atom = { ident "[" ident "]" | constant | number }
    let mut it = p.into_inner();
    let first = it.next().unwrap();
    match first.as_rule() {
        Rule::ident => {
            let name = first.as_str();
            let mid  = it.next().unwrap(); // '[' ident ']'
            let id2  = mid.as_str();
            let full = format!("{name}[{id2}]");
            Ok(Expression::Literal(Lit::Atom(full)))
        }
        Rule::constant => parse_constant(first),
        Rule::number   => Ok(Expression::Literal(Lit::Atom(first.as_str().to_string()))),
        _ => Err("bad hltl_atom".into()),
    }
}

// === ALTL chain (same precedence) ===

fn parse_aequal(p: Pair<Rule>) -> Result<Expression, String> {
    let mut it = p.into_inner();
    let left = parse_aimpl(it.next().unwrap())?;
    if let Some(eq_tail) = it.next() {
        let right = parse_aequal(eq_tail)?;
        Ok(Expression::Iff(Box::new(left), Box::new(right)))
    } else { Ok(left) }
}
fn parse_aimpl(p: Pair<Rule>) -> Result<Expression, String> {
    let mut it = p.into_inner();
    let left = parse_adisj(it.next().unwrap())?;
    if let Some(next) = it.next() {
        let right = parse_aimpl(next)?;
        Ok(Expression::Implies(Box::new(left), Box::new(right)))
    } else { Ok(left) }
}
fn parse_adisj(p: Pair<Rule>) -> Result<Expression, String> {
    let mut it = p.into_inner();
    let left = parse_aconj(it.next().unwrap())?;
    if let Some(next) = it.next() {
        let right = parse_adisj(next)?;
        Ok(Expression::Or(Box::new(left), Box::new(right)))
    } else { Ok(left) }
}
fn parse_aconj(p: Pair<Rule>) -> Result<Expression, String> {
    let mut it = p.into_inner();
    let left = parse_auntl(it.next().unwrap())?;
    if let Some(next) = it.next() {
        let right = parse_aconj(next)?;
        Ok(Expression::And(Box::new(left), Box::new(right)))
    } else { Ok(left) }
}
fn parse_auntl(p: Pair<Rule>) -> Result<Expression, String> {
    let mut it = p.into_inner();
    let left = parse_arels(it.next().unwrap())?;
    if let Some(next) = it.next() {
        let right = parse_auntl(next)?;
        Ok(Expression::U(Box::new(left), Box::new(right)))
    } else { Ok(left) }
}
fn parse_arels(p: Pair<Rule>) -> Result<Expression, String> {
    let mut it = p.into_inner();
    let left = parse_afactor(it.next().unwrap())?;
    if let Some(next) = it.next() {
        let right = parse_arels(next)?;
        Ok(Expression::R(Box::new(left), Box::new(right)))
    } else { Ok(left) }
}
fn parse_afactor(p: Pair<Rule>) -> Result<Expression, String> {
    // afactor = { aunop ~ afactor | "(" ~ inner_altl ~ ")" | altl_atom }
    let mut it = p.into_inner();
    let first = it.next().unwrap();
    match first.as_rule() {
        Rule::aunop => {
            let op = first.as_str();
            let rhs = parse_afactor(it.next().unwrap())?;
            Ok(match op {
                "G" => Expression::G(Box::new(rhs)),
                "F" => Expression::F(Box::new(rhs)),
                "~" => Expression::Neg(Box::new(rhs)),
                _   => return Err(format!("unknown aunop {op}")),
            })
        }
        Rule::inner_altl => parse_inner_altl(first),
        Rule::altl_atom  => parse_altl_atom(first),
        _ => Err("bad afactor".into()),
    }
}
fn parse_altl_atom(p: Pair<Rule>) -> Result<Expression, String> {
    // altl_atom = { ident "[" ident "]" "[" ident "]" | constant | number}
    let mut it = p.into_inner();
    let first = it.next().unwrap();
    match first.as_rule() {
        Rule::ident => {
            let name = first.as_str();
            let mid1 = it.next().unwrap(); // "[" ident "]"
            let id1  = mid1.as_str();
            let mid2 = it.next().unwrap(); // "[" ident "]"
            let id2  = mid2.as_str();
            let full = format!("{name}[{id1}][{id2}]");
            Ok(Expression::Literal(Lit::Atom(full)))
        }
        Rule::constant => parse_constant(first),
        Rule::number   => Ok(Expression::Literal(Lit::Atom(first.as_str().to_string()))),
        _ => Err("bad altl_atom".into()),
    }
}

fn parse_constant(p: Pair<Rule>) -> Result<Expression, String> {
    match p.as_str() {
        "TRUE"  => Ok(Expression::Literal(Lit::Atom("true".into()))),
        "FALSE" => Ok(Expression::Literal(Lit::NegAtom("true".into()))),
        _ => Err(format!("unknown constant {}", p.as_str())),
    }
}