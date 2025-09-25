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
    pub ahltl_expr: Expression,
    pub all_phi_pos: Vec<(TrajQuant, Expression)>, 
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
    let inner = parse_form_rec(after_paths)?;
    let inner = bitblast_eqs(&inner, max_bit_map);

    println!("\nPath Prefix:  {:?} ", prefix);
    println!("\nTrajectories: {:?}", trajs);
    println!("\nInner LTL:    {:?}", inner);

    // 4) Build the AHLTL encoding (parameterize k as needed)
    let k = bound;
    // let (ahltl_expr, pos_prefix) = build_ahltl_with_selectors(&prefix, &trajs, &inner_formula, bound);
    // let pos_prefix: Vec<(Quant, Vec<String>)> = build_traj_position_prefix(&trajs, &inner, k);
    // println!("\nPositions:  {:?}", pos_prefix);
    // println!("\nConstraints: {:?}", expression_to_string(&ahltl_expr));

    let all_phi_pos =  build_phi_pos(&prefix, &trajs, k);
    let ahltl_expr  = translate_all_inner_ahltl(&inner, &prefix, &trajs, k);

    // println!("\nPHI_pos: \n{:?}", phi_pos);
    // println!("\nAHLTL:    {:?}", ahltl_expr);    


    Ok(AHLTLParsed { prefix, trajs, ahltl_expr, all_phi_pos})
    // Ok(AHLTLParsed { prefix, trajs, pos_prefixes, ahltl_expr})

}

/// Parse "foo[A][t]" → ("foo", Some("A"), Some("t"))  (very lightweight)
fn split_base_path_time(s: &str) -> (String, Option<String>, Option<String>) {
    // expected formats:  base, base[path], base[path][time]
    // we don't panic on odd inputs; we just return base untouched.
    let mut base = s.to_string();
    let mut path = None;
    let mut time = None;

    if let Some(i) = s.find('[') {
        base = s[..i].to_string();
        let rest = &s[i..]; // like "[A][t]" or "[A]" or "[0]"
        let mut parts = rest.split(']').filter(|p| !p.is_empty());
        // each part looks like "[A" or "[t"
        if let Some(p1) = parts.next() {
            path = Some(p1.trim_start_matches('[').to_string());
        }
        if let Some(p2) = parts.next() {
            time = Some(p2.trim_start_matches('[').to_string());
        }
    }
    (base, path, time)
}

/// Build the stamped atom p^i_π:
/// Input atom is something like Literal(Atom("line[A][t]")) or "halt[A][t]".
/// We rewrite to "base[path][i]".
fn make_stamp_atom() -> impl Fn(&Expression, usize, &str) -> Expression {
    move |atom: &Expression, i: usize, path: &str| {
        match atom {
            Expression::Literal(Lit::Atom(name)) |
            Expression::Literal(Lit::NegAtom(name)) => {
                let (base, _, _) = split_base_path_time(name);
                // let stamped = format!("{}[{}][{}]", base, path, i);
                let stamped = format!("{}[{}][{}]", base, path, i);
                // NOTE: translate_inner_ahltl only calls this for *positive* atoms,
                // it handles ¬p by passing `is_neg=true` internally.
                Literal(Lit::Atom(stamped))
            }
            other => {
                // If your atoms can be more structured, adapt here.
                // Fallback: leave as-is.
                other.clone()
            }
        }
    }
}

/// halted^m_π  as a literal, e.g. "halt[path][m]"
fn make_halted_at_m() -> impl Fn(&str, usize) -> Expression {
    move |path: &str, m: usize| {
        // Literal(Lit::Atom(format!("halt[{}][{}]", path, m)))
        Literal(Lit::Atom(format!("halt[{}][{}]", path, (m/2))))
    }
}

// ----- 2) How to call the translator ----- //

/// Build the full conjunction  ∧_{π∈paths} ∧_{τ∈trajs} ∧_{j∈0..m}  ⟦inner⟧^{j}_{k,m}[π,τ]
pub fn translate_all_inner_ahltl(
    inner: &Expression,
    prefix: &[(Quant, String)],         // paths
    trajs:  &[(TrajQuant, String)],     // trajectories
    k: usize,
) -> Expression {
    let m = 2 * k; // typical choice; change if you need a different m
    let stamp_atom   = make_stamp_atom();
    let halted_at_m  = make_halted_at_m();

    let mut clauses: Vec<Box<Expression>> = Vec::new();

    // we only need the path *names*
    let paths: Vec<&str> = prefix.iter().map(|(_, p)| p.as_str()).collect();

    for j in 0..=m {
        for &(_, ref tau) in trajs {
            for &pi in &paths {
                let translated = translate_inner_ahltl(
                    inner,    // ⟦inner⟧
                    pi,       // π
                    tau,      // τ
                    j,        // j
                    k,        // k
                    m,        // m
                    &stamp_atom,
                    &halted_at_m,
                );
                clauses.push(Box::new(translated));
            }
        }
    }

    match clauses.len() {
        0 => True,
        1 => *clauses.pop().unwrap(),
        _ => MAnd(clauses),
    }
}


// Example: turn `Literal(Atom("line[A][t]"))` into `Literal(Atom(format!("line[{}][{}]", path, i)))`
type StampAtomFn = dyn Fn(&Expression, usize, &str) -> Expression;

/// Translate an inner AHLTL formula ⟦φ⟧^{j}_{k,m} for a fixed path π, trajectory τ.
///
/// Implements rules:
/// (14)  ⟦p_{π,τ}⟧^j   =  ⋁_{i∈0..k} ( pos^{i,j}_{π,τ} ∧ p^i_π )
/// (15)  ⟦¬p_{π,τ}⟧^j  =  ⋁_{i∈0..k} ( pos^{i,j}_{π,τ} ∧ ¬p^i_π )
/// (16)  ⟦ψ₁ ∨ ψ₂⟧^j   =  ⟦ψ₁⟧^j ∨ ⟦ψ₂⟧^j
/// (17)  ⟦ψ₁ ∧ ψ₂⟧^j   =  ⟦ψ₁⟧^j ∧ ⟦ψ₂⟧^j
/// (18)  ⟦ψ₁ U ψ₂⟧^j   =  ¬off^j ∧ ( ⟦ψ₂⟧^j ∨ (⟦ψ₁⟧^j ∧ ⟦ψ₁ U ψ₂⟧^{j+1}) ), for j < m
/// (19)  ⟦ψ₁ R ψ₂⟧^j   =  ¬off^j ∧ ( ⟦ψ₁⟧^j ∨ (⟦ψ₂⟧^j ∧ ⟦ψ₁ R ψ₂⟧^{j+1}) ), for j < m
/// (20)  ⟦ψ₁ U ψ₂⟧^m   =  ⟦ψ₂⟧^m
/// (21)  ⟦ψ₁ R ψ₂⟧^m   =  (⟦ψ₁⟧^m ∧ ⟦ψ₂⟧^m) ∨ (halted^m_π ∧ ⟦ψ₂⟧^m)
///
/// `stamp_atom(p,i,path)` must produce the propositional instance p^i_π.
/// `halted_at_m(path, m)` must produce the literal for halted^m_π.
pub fn translate_inner_ahltl(
    phi: &Expression,             // inner AHLTL subformula
    path: &str,                   // π
    traj: &str,                   // τ
    j: usize,                     // current j (0..m)
    k: usize,                     // unrolling k
    m: usize,                     // m (usually 2k)
    stamp_atom: &dyn Fn(&Expression, usize, &str) -> Expression,
    halted_at_m: &dyn Fn(&str, usize) -> Expression,
) -> Expression {
    // helpers to build pos^{i,j}_{π,τ} and off^{j}_{π,τ}
    let pos_ij = |i: usize, j: usize| -> Expression {
        Literal(Lit::Atom(pos_name(path, traj, i, j)))
    };
    let off_j = |j: usize| -> Expression {
        Literal(Lit::Atom(off_name(path, traj, j)))
    };

    // atomic (rule 14/15): for Literal/Neg(Literal)
    let translate_atomic_at_j = |atom: &Expression, is_neg: bool| -> Expression {
        // big OR over i=0..k of (pos^{i,j}_{π,τ} ∧ (± p^i_π))
        let mut lanes: Vec<Box<Expression>> = Vec::with_capacity(k + 1);
        for i in 0..=k {
            let stamped = stamp_atom(atom, i, path); // p^i_π
            let p_i = if is_neg {
                Neg(Box::new(stamped))
            } else {
                stamped
            };
            lanes.push(Box::new(And(
                Box::new(pos_ij(i, j)),
                Box::new(p_i),
            )));
        }
        match lanes.len() {
            0 => False,
            1 => *lanes.pop().unwrap(),
            _ => MOr(lanes),
        }
    };

    // main recursive worker
    fn go(
        phi: &Expression,
        path: &str,
        traj: &str,
        j: usize,
        k: usize,
        m: usize,
        pos_ij: &dyn Fn(usize, usize) -> Expression,
        off_j: &dyn Fn(usize) -> Expression,
        stamp_atom: &dyn Fn(&Expression, usize, &str) -> Expression,
        halted_at_m: &dyn Fn(&str, usize) -> Expression,
        translate_atomic_at_j: &dyn Fn(&Expression, bool) -> Expression,
    ) -> Expression {
        use Expression::*;

        match phi {
            // Boolean constants propagate
            True  => True,
            False => False,

            // Atoms / negated atoms use (14)/(15)
            Literal(Lit::Atom(_))       => translate_atomic_at_j(phi, false),
            Literal(Lit::NegAtom(_))    => {
                // treat as ¬p
                // convert to inner atom without the neg, then mark is_neg = true
                if let Literal(Lit::NegAtom(v)) = phi {
                    translate_atomic_at_j(&Literal(Lit::Atom(v.clone())), true)
                } else { unreachable!() }
            }

            // Boolean structure (16)/(17)
            Or(a, b)  => Or(
                Box::new(go(a, path, traj, j, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j)),
                Box::new(go(b, path, traj, j, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j)),
            ),
            And(a, b) => And(
                Box::new(go(a, path, traj, j, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j)),
                Box::new(go(b, path, traj, j, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j)),
            ),
            MOr(xs) => MOr(xs.iter()
                .map(|x| Box::new(go(x, path, traj, j, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j)))
                .collect()),
            MAnd(xs) => MAnd(xs.iter()
                .map(|x| Box::new(go(x, path, traj, j, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j)))
                .collect()),

            // Implication / Iff – translate structurally via →,↔ over translated subterms
            Implies(a, b) => Implies(
                Box::new(go(a, path, traj, j, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j)),
                Box::new(go(b, path, traj, j, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j)),
            ),
            Iff(a, b) => Iff(
                Box::new(go(a, path, traj, j, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j)),
                Box::new(go(b, path, traj, j, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j)),
            ),

            // Negation over non-atom: push through recursively (¬φ becomes syntactic ¬⟦φ⟧)
            Neg(x) => Neg(Box::new(go(x, path, traj, j, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j))),

            // Temporal: U / R with j < m (18)/(19) and edge at j = m (20)/(21)
            U(a, b) => {
                if j < m {
                    let not_off = Neg(Box::new(off_j(j)));
                    let psi2_j  = go(b, path, traj, j,   k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j);
                    let psi1_j  = go(a, path, traj, j,   k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j);
                    let rec     = go(&U(a.clone(), b.clone()), path, traj, j+1, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j);
                    And(Box::new(not_off), Box::new(Or(Box::new(psi2_j), Box::new(And(Box::new(psi1_j), Box::new(rec))))))
                } else {
                    // j == m: rule (20)
                    go(b, path, traj, m, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j)
                }
            }

            R(a, b) => {
                if j < m {
                    let not_off = Neg(Box::new(off_j(j)));
                    let psi1_j  = go(a, path, traj, j,   k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j);
                    let psi2_j  = go(b, path, traj, j,   k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j);
                    let rec     = go(&R(a.clone(), b.clone()), path, traj, j+1, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j);
                    And(Box::new(not_off), Box::new(Or(Box::new(psi1_j), Box::new(And(Box::new(psi2_j), Box::new(rec))))))
                } else {
                    // j == m: rule (21)
                    let psi1_m = go(a, path, traj, m, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j);
                    let psi2_m = go(b, path, traj, m, k, m, pos_ij, off_j, stamp_atom, halted_at_m, translate_atomic_at_j);
                    let halted = halted_at_m(path, m);
                    Or(
                        Box::new(And(Box::new(psi1_m.clone()), Box::new(psi2_m.clone()))),
                        Box::new(And(Box::new(halted), Box::new(psi2_m))),
                    )
                }
            }

            // F ψ  ≡  True U ψ
            F(psi) => {
                let desugared = U(Box::new(True), psi.clone());
                return translate_inner_ahltl(
                    &desugared, path, traj, j, k, m, stamp_atom, halted_at_m
                );
            }

            // G ψ  ≡  False R ψ
            G(psi) => {
                let desugared = R(Box::new(False), psi.clone());
                return translate_inner_ahltl(
                    &desugared, path, traj, j, k, m, stamp_atom, halted_at_m
                );
            }

            // X ψ :
            //  for j < m :  (¬off^j_{π,τ}) ∧ ⟦ψ⟧^{j+1}_{k,m}
            //  for j = m :  (halted^m_π) ∧ ⟦ψ⟧^{m}_{k,m}    (pessimistic halting)
            X(psi) => {
                if j < m {
                    let not_off_j = Expression::Neg(Box::new(Literal(Lit::Atom(off_name(path, traj, j)))));
                    let next = translate_inner_ahltl(
                        psi, path, traj, j + 1, k, m, stamp_atom, halted_at_m
                    );
                    return Expression::And(Box::new(not_off_j), Box::new(next));
                } else {
                    let halted_m = halted_at_m(path, m);
                    let stay = translate_inner_ahltl(
                        psi, path, traj, m, k, m, stamp_atom, halted_at_m
                    );
                    return Expression::And(Box::new(halted_m), Box::new(stay));
                }
            }
        }
    }

    go(
        phi, path, traj, j, k, m,
        &pos_ij, &off_j, stamp_atom, halted_at_m,
        &translate_atomic_at_j,
    )
}



/// Helper (same naming style):
#[inline]
fn pos_name(path: &str, traj: &str, i: usize, j: usize) -> String {
    format!("pos_{}_{:}_{}_{:}", i, j, path, traj)
}

#[inline]
fn off_name(path: &str, traj: &str, j: usize) -> String {
    format!("off_{}_{:}", path, traj)  // or: format!("off_{}_{:}", j, path, traj)
}

#[inline]
fn t_name(path: &str, traj: &str, j: usize) -> String {
    // e.g., "t_A_0_tauX" or simply "t_A_0" if you don't want traj in the name.
    // Match whatever convention you decided—here we include both:
    format!("t_{}_{}_{}", path, j, traj)
}

/// Build:  pos(i,j,π,τ) ∧ (∧_{n!=i} ¬pos(n,j,π,τ)) ∧ ¬off(j,π,τ)
pub fn build_setpos(path: &str, traj: &str, i: usize, j: usize, k: usize) -> Expression {
    // head: pos(i,j,π,τ)
    let head = Literal(Lit::Atom(pos_name(path, traj, i, j)));

    // all other n in 0..=k except i  →  ¬pos(n,j,π,τ)
    let mut exclusives: Vec<Box<Expression>> = Vec::with_capacity(k.saturating_add(1));
    for n in 0..=k {
        if n == i { continue; }
        let p = Literal(Lit::Atom(pos_name(path, traj, n, j)));
        exclusives.push(Box::new(Neg(Box::new(p))));
    }
    let others = if exclusives.is_empty() {
        // if k == 0 and i==0, this block is vacuous → True
        Expression::True
    } else {
        Expression::MAnd(exclusives)
    };

    // ¬off(j,π,τ)
    let off = Neg(Box::new(Literal(Lit::Atom(off_name(path, traj, j)))));

    // pos(i,j,π,τ) ∧ (∧_{n!=i} ¬pos(n,j,π,τ)) ∧ ¬off(j,π,τ)
    Expression::And(
        Box::new(head),
        Box::new(Expression::And(Box::new(others), Box::new(off))),
    )
}


/// Build: off(j,π,τ) ∧ (∧_{n=0..k} ¬pos(n,j,π,τ))
pub fn build_nopos(path: &str, traj: &str, j: usize, k: usize) -> Expression {
    // off(j,π,τ)
    let off = Literal(Lit::Atom(off_name(path, traj, j)));

    // ∧_{n=0..k} ¬pos(n,j,π,τ)
    let mut neg_pos: Vec<Box<Expression>> = Vec::with_capacity(k + 1);
    for n in 0..=k {
        let p = Literal(Lit::Atom(pos_name(path, traj, n, j)));
        neg_pos.push(Box::new(Neg(Box::new(p))));
    }
    let no_positions = if neg_pos.is_empty() {
        Expression::True
    } else {
        Expression::MAnd(neg_pos)
    };

    // Combine: off ∧ no_positions
    Expression::And(Box::new(off), Box::new(no_positions))
}



/// step^j_{π,τ} := ∧_{i=0..k-1} ( (pos^{i,j}_{π,τ} ∧ t^{j}_{π}) → setpos^{i+1,j+1}_{π,τ} )
pub fn build_step(path: &str, traj: &str, j: usize, k: usize) -> Expression {
    // If k == 0 or 1, the range 0..k-1 is empty → conjunction over empty set = True
    if k == 0 || k == 1 {
        return Expression::True;
    }

    let t_j = Literal(Lit::Atom(t_name(path, traj, j)));

    let mut clauses: Vec<Box<Expression>> = Vec::with_capacity(k.saturating_sub(1));
    for i in 0..(k - 1) {
        // (pos^{i,j}_{π,τ} ∧ t^{j}_{π})
        let pos_ij = Literal(Lit::Atom(pos_name(path, traj, i, j)));
        let lhs = And(Box::new(pos_ij), Box::new(t_j.clone()));

        // setpos^{i+1,j+1}_{π,τ}  (calls your previously defined builder)
        let rhs = build_setpos(path, traj, i + 1, j + 1, k);

        // implication
        clauses.push(Box::new(Implies(Box::new(lhs), Box::new(rhs))));
    }

    // Big ∧ over all i
    if clauses.is_empty() {
        Expression::True
    } else if clauses.len() == 1 {
        *clauses.pop().unwrap()
    } else {
        Expression::MAnd(clauses)
    }
}


/// stutters^j_{π,τ} := ∧_{i=0..k} ( (pos^{i,j}_{π,τ} ∧ ¬t^{j}_{π}) → setpos^{i, j+1}_{π,τ} )
pub fn build_stutters(path: &str, traj: &str, j: usize, k: usize) -> Expression {
    let t_j  = Literal(Lit::Atom(t_name(path, traj, j)));
    let not_tj = Neg(Box::new(t_j.clone()));

    let mut clauses: Vec<Box<Expression>> = Vec::with_capacity(k + 1);
    for i in 0..=k {
        // (pos^{i,j}_{π,τ} ∧ ¬t^{j}_{π})
        let pos_ij = Literal(Lit::Atom(pos_name(path, traj, i, j)));
        let lhs = And(Box::new(pos_ij), Box::new(not_tj.clone()));

        // setpos^{i, j+1}_{π,τ}
        let rhs = build_setpos(path, traj, i, j + 1, k);

        clauses.push(Box::new(Implies(Box::new(lhs), Box::new(rhs))));
    }

    // Big ∧ over all i
    if clauses.is_empty() {
        True
    } else if clauses.len() == 1 {
        *clauses.pop().unwrap()
    } else {
        MAnd(clauses)
    }
}


#[inline]
fn halt_name(path: &str, k: usize) -> String {
    // Match your naming, e.g., "halt[A][k]" → "halt_A_k" or similar.
    format!("halt[{}][{}]", path, k)
}



/// ends^j_{π,τ} := (pos^{k,j}_{π,τ} ∧ t^j_π) → ((¬halt^k_π → nopos^{j+1}_{π,τ}) ∧ (halt^k_π → setpos^{k,j+1}_{π,τ}))
pub fn build_ends(path: &str, traj: &str, j: usize, k: usize) -> Expression {
    // Antecedent: pos^{k,j}_{π,τ} ∧ t^{j}_{π}
    let pos_kj = Literal(Lit::Atom(pos_name(path, traj, k, j)));
    let t_j    = Literal(Lit::Atom(t_name(path, traj, j)));
    let antecedent = And(Box::new(pos_kj), Box::new(t_j));

    // Consequent part 1: (¬halt^k_π → nopos^{j+1}_{π,τ})
    let halt_k   = Literal(Lit::Atom(halt_name(path, k)));
    let not_halt = Neg(Box::new(halt_k.clone()));
    let nopos_j1 = build_nopos(path, traj, j + 1, k);
    let c1 = Implies(Box::new(not_halt), Box::new(nopos_j1));

    // Consequent part 2: (halt^k_π → setpos^{k, j+1}_{π,τ})
    let setpos_k_j1 = build_setpos(path, traj, k, j + 1, k);
    let c2 = Implies(Box::new(halt_k), Box::new(setpos_k_j1));

    let consequent = And(Box::new(c1), Box::new(c2));

    Implies(Box::new(antecedent), Box::new(consequent))
}


/// Build I_pos = ⋀_{paths,trajs} pos_0_0_{path,traj}
/// I_pos for a *single* trajectory τ:  ∧_{π ∈ paths} pos_{0,0,π,τ}
fn build_ipos_for_traj(paths: &[(Quant, String)], tname: &str) -> Expression {
    let mut conj: Vec<Box<Expression>> = Vec::with_capacity(paths.len());
    for (_, path) in paths {
        let p = pos_name(path, tname, 0, 0);
        conj.push(Box::new(Literal(Lit::Atom(p))));
    }
    match conj.len() {
        0 => Expression::True,
        1 => *conj.pop().unwrap(),
        _ => MAnd(conj),
    }
}

/// Build ϕ_pos given:
/// - `paths`:   list of path names (e.g., ["A","B",...])
/// - `trajs`:   list of (quant, traj_name); we only need the name here
/// - `k`:       path bound
/// - `ipos`:    the initial-position constraints I_pos (already built elsewhere)
///
/// Convention: j ranges 0..=2k (m = 2k).
pub fn build_phi_pos(
    paths: &[(Quant, String)],
    trajs: &[(TrajQuant, String)],
    k: usize,
) -> Vec<(TrajQuant, Expression)> {
    let m = 2 * k;
    let mut out: Vec<(TrajQuant, Expression)> = Vec::with_capacity(trajs.len());

    for (tq, tname) in trajs {
        // I_pos scoped to this trajectory
        let ipos_tau = build_ipos_for_traj(paths, tname);

        // ⋀ over j and paths of (step ∧ stutters ∧ ends)
        let mut conj: Vec<Box<Expression>> = Vec::new();
        for j in 0..=m {
            for (_, path) in paths {
                let step_j     = build_step(path, tname, j, k);
                let stutters_j = build_stutters(path, tname, j, k);
                let ends_j     = build_ends(path, tname, j, k);

                let triple = And(
                    Box::new(step_j),
                    Box::new(And(Box::new(stutters_j), Box::new(ends_j))),
                );
                conj.push(Box::new(triple));
            }
        }

        let body = match conj.len() {
            0 => ipos_tau,
            1 => And(Box::new(ipos_tau), conj.pop().unwrap()),
            _ => And(Box::new(ipos_tau), Box::new(MAnd(conj))),
        };

        out.push((*tq, body));
    }

    out
}

/// ==============================================================================



/// Map TrajQuant to Quant for headers
fn tq_to_q(tq: TrajQuant) -> Quant {
    match tq {
        TrajQuant::TrajA => Quant::Forall,
        TrajQuant::TrajE => Quant::Exists,
    }
}

/// Parse an atom name like `name[Path][t]` → (base, path, traj).
/// Returns None if it doesn't match that shape.
fn parse_atom_path_traj(s: &str) -> Option<(String, String, String)> {
    // Fast path: must contain two bracket pairs.
    let bytes = s.as_bytes();
    let mut opens = Vec::with_capacity(2);
    let mut closes = Vec::with_capacity(2);
    for (i, &b) in bytes.iter().enumerate() {
        if b == b'[' { opens.push(i); }
        if b == b']' { closes.push(i); }
    }
    if opens.len() < 2 || closes.len() < 2 { return None; }
    // base = before first '['
    let base = s[..opens[0]].to_string();
    let path = s[opens[0]+1..closes[0]].to_string();
    let traj = s[opens[1]+1..closes[1]].to_string();
    if base.is_empty() || path.is_empty() || traj.is_empty() {
        return None;
    }
    Some((base, path, traj))
}

/// Collect map: traj_name -> set of paths that appear with that traj in `inner`.
fn collect_traj_path_assoc(inner: &Expression) -> HashMap<String, HashSet<String>> {
    use Expression::*;
    let mut map: HashMap<String, HashSet<String>> = HashMap::new();

    fn visit(e: &Expression, map: &mut HashMap<String, HashSet<String>>) {
        use Expression::*;
        match e {
            Literal(Lit::Atom(v)) | Literal(Lit::NegAtom(v)) => {
                if let Some((_base, path, traj)) = parse_atom_path_traj(v) {
                    map.entry(traj).or_default().insert(path);
                }
            }
            Neg(x) | G(x) | F(x) | X(x) => visit(x, map),
            And(a,b) | Or(a,b) | U(a,b) | R(a,b) | Iff(a,b) | Implies(a,b) => {
                visit(a, map); visit(b, map);
            }
            MAnd(xs) | MOr(xs) => for x in xs { visit(x, map); }
            True | False => {}
        }
    }

    visit(inner, &mut map);
    map
}

/// Build position-variable header blocks for trajectories.
/// For each (traj, paths_associated), create names `pos_{i}_{j}_{path}_{traj}`
/// with i ∈ [0..k], j ∈ [0..2k], and Quant derived from TrajQuant.
/// Returns: Vec of (Quant, Vec<String>) — one entry per trajectory.
pub fn build_traj_position_prefix(
    trajs: &[(TrajQuant, String)],
    inner: &Expression,
    k: usize,
) -> Vec<(Quant, Vec<String>)> {
    let assoc = collect_traj_path_assoc(inner);

    let mut out: Vec<(Quant, Vec<String>)> = Vec::new();
    for (tq, tname) in trajs {
        // Which paths actually occur with this trajectory in the formula?
        let Some(paths) = assoc.get(tname) else {
            // No association found for this traj in the inner formula — skip.
            continue;
        };

        let mut names = Vec::with_capacity(paths.len() * (k+1) * (2*k + 1));
        for path in paths {
            for i in 0..=k {
                for j in 0..=(2*k) {
                    names.push(format!("pos_{}_{}_{}_{}", i, j, path, tname));
                }
            }
        }

        if !names.is_empty() {
            out.push((tq_to_q(*tq), names));
        }
    }

    out
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
    format!("pos_{}_{}", path, i)
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
        let sel  = format!("pos_{}_{}", path, i);
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
            prefix_ext.push((Quant::Exists, format!("pos_{}_{}", path, i)));
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
// pub fn selectify_wrt_trajectories(
//     e: &Expression,
//     paths: &[&str],
//     traj_var: &str,
//     k: usize,
//     out_exist_selectors: &mut Vec<String>,
// ) -> Expression {
//     // Precompute selector names and remember them for quantification
//     let mut path_to_selectors: HashMap<String, Vec<String>> = HashMap::new();
//     for &p in paths {
//         let mut sels = Vec::with_capacity(k + 1);
//         for i in 0..=k {
//             let s = sel_name(p, i);
//             sels.push(s.clone());
//             out_exist_selectors.push(s);
//         }
//         path_to_selectors.insert(p.to_string(), sels);
//     }

//     fn go(
//         e: &Expression,
//         traj_var: &str,
//         k: usize,
//         path_to_selectors: &HashMap<String, Vec<String>>,
//     ) -> Expression {
//         use Expression::*;
//         match e {
//             // Atom / NegAtom cases: check if it is NAME[PATH][traj_var]
//             Expression::Literal(Lit::Atom(v)) => {
//                 if let Some((base, path, time)) = parse_base_path_time(v) {
//                     if time == traj_var {
//                         if let Some(_selset) = path_to_selectors.get(&path) {
//                             // ∨_i (s_path_i <-> base[path][i])
//                             let lanes = (0..=k).map(|i| lane_iff(&base, &path, i, false)).collect();
//                             return big_or(lanes);
//                         }
//                     }
//                 }
//                 // otherwise keep as is
//                 e.clone()
//             }
//             Expression::Literal(Lit::NegAtom(v)) => {
//                 if let Some((base, path, time)) = parse_base_path_time(v) {
//                     if time == traj_var {
//                         if let Some(_selset) = path_to_selectors.get(&path) {
//                             // ∨_i (s_path_i <-> ¬base[path][i])
//                             let lanes = (0..=k).map(|i| lane_iff(&base, &path, i, true)).collect();
//                             return big_or(lanes);
//                         }
//                     }
//                 }
//                 e.clone()
//             }

//             // Structural recursion
//             Neg(x) => Neg(Box::new(go(x, traj_var, k, path_to_selectors))),
//             And(a,b) => And(
//                 Box::new(go(a, traj_var, k, path_to_selectors)),
//                 Box::new(go(b, traj_var, k, path_to_selectors)),
//             ),
//             Or(a,b) => Or(
//                 Box::new(go(a, traj_var, k, path_to_selectors)),
//                 Box::new(go(b, traj_var, k, path_to_selectors)),
//             ),
//             Iff(a,b) => Iff(
//                 Box::new(go(a, traj_var, k, path_to_selectors)),
//                 Box::new(go(b, traj_var, k, path_to_selectors)),
//             ),
//             Implies(a,b) => Implies(
//                 Box::new(go(a, traj_var, k, path_to_selectors)),
//                 Box::new(go(b, traj_var, k, path_to_selectors)),
//             ),
//             MAnd(xs) => MAnd(xs.iter().map(|x| Box::new(go(x, traj_var, k, path_to_selectors))).collect()),
//             MOr(xs)  => MOr(xs.iter().map(|x| Box::new(go(x, traj_var, k, path_to_selectors))).collect()),

//             // If you keep temporal nodes in this representation, recurse into them too:
//             G(x) => G(Box::new(go(x, traj_var, k, path_to_selectors))),
//             F(x) => F(Box::new(go(x, traj_var, k, path_to_selectors))),
//             X(x) => X(Box::new(go(x, traj_var, k, path_to_selectors))),
//             U(a,b)=> U(Box::new(go(a, traj_var, k, path_to_selectors)),
//                        Box::new(go(b, traj_var, k, path_to_selectors))),
//             R(a,b)=> R(Box::new(go(a, traj_var, k, path_to_selectors)),
//                        Box::new(go(b, traj_var, k, path_to_selectors))),

//             True | False => e.clone(),
//         }
//     }

//     go(e, traj_var, k, &path_to_selectors)
// }



















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