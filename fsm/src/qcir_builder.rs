use std::collections::VecDeque;
use expressions::{Expression, Literal as Lit, Variable, Quant};
use expressions::expression_to_string;
use std::fmt::Write as FmtWrite;
use logging::Logger;
use crate::parser::split_on_value;
use crate::symbol_map::SymbolMap;
use stacker;
use std::collections::{HashMap, HashSet};
use expressions::TrajQuant;


// ---------- QCIR builder ----------
// New version: Sep. 2025

pub type PredMap = HashMap<String, Expression>;

#[derive(Debug)]
pub enum LowerError { Temporal(&'static str) }

#[derive(Default)]
pub struct QcirBuilder {
    next_gate: usize,
    defs: Vec<String>,                        // e.g., "g3 = and(g1, g2)"
    memo: std::collections::HashMap<Expression, isize>,         // Expression -> gate id
    var_ids: HashMap<Variable, usize>,        // Variable -> gate id
    var_order: Vec<Variable>,
    seen: HashSet<Variable>,
    var_by_id: std::collections::HashMap<usize, Variable>, // id -> Variable  (NEW)
    // aux for constants, etc.
    const_var: Option<usize>,
    aux_vars: std::collections::BTreeSet<usize>,
    // NEW: debug toggle
    debug: bool,
}

impl QcirBuilder {
    pub fn new() -> Self { Self::default() }
    pub fn gate_defs(&self) -> &[String] { &self.defs }
    pub fn var_map(&self) -> &HashMap<Variable, usize> { &self.var_ids }
    pub fn with_debug(debug: bool) -> Self { Self { debug, ..Default::default() } } 

    // ---------- helpers: ids, printing, synthetic vars ----------
    #[inline]
    fn fresh(&mut self) -> usize { self.next_gate += 1; self.next_gate }

    #[inline]
    fn new_gate(&mut self) -> isize { self.fresh() as isize } // always positive

    #[inline]
    fn fmt_atom(&self, id: usize) -> String {
        if self.debug {
            if let Some(v) = self.var_by_id.get(&id) {
                // keep synthetic hidden as gN even in debug
                if !Self::is_synth(v) {
                    return v.to_string();
                }
            }
        }
        format!("{}", id)
    }

    #[inline]
    fn fmt_lit(&self, id: isize) -> String {
        if id < 0 {
            format!("-{}", self.fmt_atom((-id) as usize))
        } else {
            self.fmt_atom(id as usize)
        }
    }

    #[inline]
    fn fmt_lits(&self, args: &[isize]) -> String {
        args.iter().map(|&x| self.fmt_lit(x))
            .collect::<Vec<_>>()
            .join(", ")
    }

    #[inline]
    pub(crate) fn is_synth(v: &Variable) -> bool {
        // If Variable is String; adapt for your type as needed
        v.as_str().starts_with('$')
    }

    // ---------- variable interning: real vars only, no gates ----------
    fn intern_var(&mut self, v: &Variable) -> usize {
        if let Some(&g) = self.var_ids.get(v) { return g; }
        let g = self.fresh();
        // keep reverse map so we can print names in debug mode
        self.var_by_id.insert(g, v.clone());

        if !Self::is_synth(v) {
            self.var_ids.insert(v.clone(), g);
            if self.seen.insert(v.clone()) { self.var_order.push(v.clone()); }
        }
        g
    }

    // ---------- constructors (now isize-based for literals) ----------
    fn mk_not(&mut self, a: isize) -> isize {
        // Inline negation: no new gate, just flip the sign
        -a
    }

    fn mk_and(&mut self, args: &[isize]) -> isize {
        match args.len() {
            0 => self.mk_true(),
            1 => args[0],
            _ => {
                let g = self.new_gate(); // positive isize
                let rhs = self.fmt_lits(args);
                // LHS remains a gate id (always printed as gN, never a name)
                self.defs.push(format!("{} = and({})", g, rhs));
                g
            }
        }
    }

    fn mk_or(&mut self, args: &[isize]) -> isize {
        match args.len() {
            0 => self.mk_false(),
            1 => args[0],
            _ => {
                let g = self.new_gate();
                let rhs = self.fmt_lits(args);
                self.defs.push(format!("{} = or({})", g, rhs));
                g
            }
        }
    }

    // Constants via synthetic vars
    // QCIR has no built-in TRUE/FALSE, using dummy variable 1 to build it. 
    fn mk_true(&mut self) -> isize {
        // let a = self.intern_var(&"$const_true".to_string()) as isize;
        // let na = self.mk_not(a);
        // self.mk_or(&[a, na])  // a ∨ ¬a
        1
    }
    fn mk_false(&mut self) -> isize {
        // let a = self.intern_var(&"$const_false".to_string()) as isize;
        // let na = self.mk_not(a);
        // self.mk_and(&[a, na]) // a ∧ ¬a
        1
    }

    // ---------- lowering: now returns isize literal/gate id ----------
    pub fn lower(&mut self, e: &Expression) -> Result<isize, LowerError> {
        if let Some(&g) = self.memo.get(e) { return Ok(g); } // memo: Expression -> isize

        use Expression::*;
        let g: isize = match e {
            True  => self.mk_true(),
            False => self.mk_false(),

            Expression::Literal(l) => match l {
                Lit::Atom(v) => {
                    // println!("[lower] Atom: {}", v);
                    self.intern_var(v) as isize
                }
                Lit::NegAtom(v) => {
                    // println!("[lower] NegAtom: {}", v);
                    let id = self.intern_var(v) as isize; // store first
                    self.mk_not(id)                       // then call mk_not
                }
            },

            // negation
            Neg(x) => match &**x {
                Literal(Lit::Atom(v))    => -(self.intern_var(v) as isize),
                Literal(Lit::NegAtom(v)) =>  (self.intern_var(v) as isize),
                _ => {
                    // lower inner to a gate id, then negate the *id*
                    let a = self.lower(x)?;
                    self.mk_not(a)
                }
            },
            // Neg(x) => {
            //     let a = self.lower(x)?;
            //     self.mk_not(a)                                        // inline minus
            // }

            And(a,b) => {
                let ga = self.lower(a)?;
                let gb = self.lower(b)?;
                self.mk_and(&[ga, gb])
            }
            MAnd(xs) => {
                let mut args = Vec::with_capacity(xs.len());
                for x in xs { args.push(self.lower(x)?); }
                self.mk_and(&args)
            }

            Or(a,b) => {
                let ga = self.lower(a)?;
                let gb = self.lower(b)?;
                self.mk_or(&[ga, gb])
            }
            MOr(xs) => {
                let mut args = Vec::with_capacity(xs.len());
                for x in xs { args.push(self.lower(x)?); }
                self.mk_or(&args)
            }

            Implies(a,b) => {
                // a → b ≡ ¬a ∨ b
                let desug = Or(Box::new(Neg(a.clone())), b.clone());
                return self.lower(&desug);
            }
            Iff(a,b) => {
                // a ↔ b ≡ (a→b) ∧ (b→a)
                let imp1 = Implies(a.clone(), b.clone());
                let imp2 = Implies(b.clone(), a.clone());
                let desug = And(Box::new(imp1), Box::new(imp2));
                return self.lower(&desug);
            }

            G(_) => return Err(LowerError::Temporal("G")),
            F(_) => return Err(LowerError::Temporal("F")),
            X(_) => return Err(LowerError::Temporal("X")),
            U(_,_) => return Err(LowerError::Temporal("U")),
            R(_,_) => return Err(LowerError::Temporal("R")),
        };

        self.memo.insert(e.clone(), g);
        Ok(g)
    }
}

//
// ---------- Base QCIR emission (no unrolling) ----------
//

/// Emit QCIR for a set of expressions, with all headers at the top.
/// If `exprs.len() == 1`, it uses that 1; otherwise it ANDs all.
/// `prefix` lists (Quant, vars) blocks in the order you want to print them.
pub fn to_qcir_string(
    init_expr: &[Expression],
    body_expr: &[Expression],
    formula_expr: &Expression,
    prefix: &[(Quant, Vec<Variable>)],
) -> Result<String, LowerError> {
    let models = init_expr
        .iter()
        .zip(body_expr.iter())
        .map(|(init, body)| {
            Expression::And(Box::new(init.clone()), Box::new(body.clone()))
        })
        .collect::<Vec<Expression>>();
    let QBF_encoding = build_QBF(&prefix, &models, &formula_expr).unwrap();
    // Initiate QcirBuilder
    let mut b = QcirBuilder::new();
    
    // b.debug = true; // <--- uncomment this to see VAR name inlined!

    // Lower the expression 
    let out = b.lower(&QBF_encoding)?;

    // Headers at the top
    let mut lines: Vec<String> = vec!["#QCIR-G14".into()];

    for (q, vars) in prefix {
        // Only print variables that actually appear in the lowered circuit.
        let ids = vars
            .iter()
            .filter_map(|nm| b.var_map().get(nm).map(|&id| {
                // When debug, prefer the actual variable name (skip synthetic like "$const")
                if b.debug && !QcirBuilder::is_synth(nm) {
                    nm.to_string()
                } else {
                    format!("{}", id)
                }
            }))
            .collect::<Vec<_>>();

        if !ids.is_empty() {
            lines.push(format!("{}({})", q.as_str(), ids.join(", ")));
        }
    }
    // Output + Gates
    lines.push(format!("output({})", out));
    lines.extend(b.gate_defs().iter().cloned());

    // footer, print variable map
    let mut entries: Vec<_> = b.var_map().iter().collect();
    Ok(lines.join("\n"))
}


/// Emit QCIR for a set of expressions, with all headers at the top.
/// If `exprs.len() == 1`, it uses that 1; otherwise it ANDs all.
/// `prefix` lists (Quant, vars) blocks in the order you want to print them.
pub fn to_async_qcir_string(
    init_expr: &[Expression],
    body_expr: &[Expression],
    formula_expr: &Expression,
    prefix: &[(Quant, Vec<Variable>)],
    traj_prefix: &[(Quant, Vec<Variable>)],
) -> Result<String, LowerError> {
    let models = init_expr
        .iter()
        .zip(body_expr.iter())
        .map(|(init, body)| {
            Expression::And(Box::new(init.clone()), Box::new(body.clone()))
        })
        .collect::<Vec<Expression>>();
    let QBF_encoding = build_async_QBF(&prefix, &models, &formula_expr, &traj_prefix).unwrap();
    // Initiate QcirBuilder
    let mut b = QcirBuilder::new();

    // b.debug = true; // <--- uncomment this to see VAR name inlined!

    // Lower the expression 
    let out = b.lower(&QBF_encoding)?;

    // PATCH: make sure elements in traj formulas are recorded
    for (_q, vars) in traj_prefix {
        for v in vars {
            b.intern_var(v); // force register trajectory vars
        }
    }

    // Headers at the top
    let mut lines: Vec<String> = vec!["#QCIR-G14".into()];

    for (q, vars) in prefix {
        // Only print variables that actually appear in the lowered circuit.
        let ids = vars
            .iter()
            .filter_map(|nm| b.var_map().get(nm).map(|&id| {
                // When debug, prefer the actual variable name (skip synthetic like "$const")
                if b.debug && !QcirBuilder::is_synth(nm) {
                    nm.to_string()
                } else {
                    format!("{}", id)
                }
            }))
            .collect::<Vec<_>>();

        if !ids.is_empty() {
            lines.push(format!("{}({})", q.as_str(), ids.join(", ")));
        }
    }

    for (q, vars) in traj_prefix {
        // println!("position var: {:?}", vars);
        // Only print variables that actually appear in the lowered circuit.
        let ids = vars
            .iter()
            .filter_map(|nm| b.var_map().get(nm).map(|&id| {
                // When debug, prefer the actual variable name (skip synthetic like "$const")
                if b.debug && !QcirBuilder::is_synth(nm) {
                    nm.to_string()
                } else {
                    format!("{}", id)
                }
            }))
            .collect::<Vec<_>>();

        if !ids.is_empty() {
            lines.push(format!("{}({})", q.as_str(), ids.join(", ")));
        }
    }

    // Output + Gates
    lines.push(format!("output({})", out));
    lines.extend(b.gate_defs().iter().cloned());

    // footer, print variable map
    let mut entries: Vec<_> = b.var_map().iter().collect();
    Ok(lines.join("\n"))
}
//
// ---------- Unrolling utilities (prime = next, time 0..k) ----------
//

/// Map "a" or "a'" at time i on PATH into "a[PATH][i]" or "a[PATH][i+1]".
fn tag_with_time(raw: &str, path: &str, i: usize) -> Variable {
    if let Some(base) = raw.strip_suffix('\'') {
        format!("{base}[{path}][{}]", i + 1) // <-- Variable constructor #1
    } else {
        format!("{raw}[{path}][{i}]")        // <-- Variable constructor #2
    }
}

fn time_tag_literal(lit: &Lit, path: &str, i: usize) -> Lit {
    match lit {
        Lit::Atom(v)    => { assert_atom_like(v); Lit::Atom(tag_with_time(v, path, i)) }
        Lit::NegAtom(v) => { assert_atom_like(v); Lit::NegAtom(tag_with_time(v, path, i))}
    }
}


fn assert_atom_like(name: &str) {
    debug_assert!(
        !name.contains('(') && !name.contains(')') &&
        !name.contains('|') && !name.contains('&') &&
        !name.contains('<') && !name.contains('>') &&
        !name.contains('=') && !name.contains('~'),
        "Found non-atomic literal: {}", name
    );
}


fn looks_non_atomic(s: &str) -> bool {
    // quick heuristic: contains operators or parentheses → not a plain var
    s.contains('(') || s.contains(')') ||
    s.contains('|') || s.contains('&') ||
    s.contains('<') || s.contains('>') ||
    s.contains('=') || s.contains('~')
}

/// Instantiate one copy of `expr` at time step `i` on `path`.
fn instantiate_once(expr: &Expression, path: &str, i: usize) -> Expression {
    use Expression::*;
    match expr {
        Literal(l) => {
            // Debug + guard before stamping
            match l {
                Lit::Atom(v) | Lit::NegAtom(v) => {
                    if looks_non_atomic(v) {
                        eprintln!(
                            "[instantiate_once][WARN] non-atomic literal before stamping: {}\n  path={}, t={}",
                            v, path, i
                        );
                        // Optional: enable this during debugging to catch sources early
                        // debug_assert!(!looks_non_atomic(v), "fake literal: {}", v);
                    }
                }
            }
            Literal(time_tag_literal(l, path, i))
        }

        Neg(x)     => Neg(Box::new(instantiate_once(x, path, i))),
        And(a,b)   => And(Box::new(instantiate_once(a, path, i)), 
                          Box::new(instantiate_once(b, path, i))),
        Or(a,b)    => Or(Box::new(instantiate_once(a, path, i)), 
                         Box::new(instantiate_once(b, path, i))),

        MAnd(xs)   => MAnd(xs.iter().map(|x| Box::new(instantiate_once(x, path, i))).collect()),
        MOr(xs)    => MOr(xs.iter().map(|x| Box::new(instantiate_once(x, path, i))).collect()),

        Implies(a,b)=> Implies(Box::new(instantiate_once(a, path, i)), Box::new(instantiate_once(b, path, i))),
        Iff(a,b)   => Iff(Box::new(instantiate_once(a, path, i)), Box::new(instantiate_once(b, path, i))),

        // Temporal nodes left structurally intact (no LTL unrolling here)
        G(x) => G(Box::new(instantiate_once(x, path, i))),
        F(x) => F(Box::new(instantiate_once(x, path, i))),
        X(x) => X(Box::new(instantiate_once(x, path, i))),
        U(a,b)=> U(Box::new(instantiate_once(a, path, i)), 
                   Box::new(instantiate_once(b, path, i))),
        R(a,b)=> R(Box::new(instantiate_once(a, path, i)), 
                   Box::new(instantiate_once(b, path, i))),

        True | False => expr.clone(),
    }
}

/// Build ∧_{i=0}^{k-1} instantiate_once(expr, PATH, i).
fn unroll_on_path(expr: &Expression, path: &str, k: usize) -> Expression {
    if k == 0 { return Expression::True; }
    let mut clauses = Vec::with_capacity(k);
    for i in 0..k {
        clauses.push(Box::new(instantiate_once(expr, path, i)));
    }
    if clauses.len() == 1 { 
        *clauses.into_iter().next().unwrap() 
    } else { Expression::MAnd(clauses) }
}

/// Unroll `expr` along `path` for k steps, substituting predicates to a fixpoint
pub fn unroll_on_path_with_preds(
    expr: &Expression,
    path: &str,
    k: usize,
    pred_map: &HashMap<String, Expression>,
) -> Expression {
    if k == 0 { return Expression::True; }

    let mut clauses: Vec<Box<Expression>> = Vec::with_capacity(k);
    for i in 0..k {
        // 1) instantiate once (stamp with [path][i])
        let inst_expanded = subst_predicates_fixpoint(expr, pred_map);
        // println!("expression: {:?}", inst_expanded);
        let inst_expr = instantiate_once(&inst_expanded, path, i);

        // 3) collect
        clauses.push(Box::new(inst_expr));
    }

    if clauses.len() == 1 {
        *clauses.into_iter().next().unwrap()
    } else {
        Expression::MAnd(clauses)
    }
}

/// Collect **time-stamped** variables syntactically from an expression.
pub fn collect_vars_unique(e: &Expression, acc: &mut HashSet<Variable>) {
    use Expression::*;
    match e {
        Literal(Lit::Atom(v)) | Literal(Lit::NegAtom(v)) => { acc.insert(v.clone()); }
        Neg(x) | G(x) | F(x) | X(x) => collect_vars_unique(x, acc),
        And(a,b) | Or(a,b) | U(a,b) | R(a,b) | Iff(a,b) | Implies(a,b) => {
            collect_vars_unique(a, acc);
            collect_vars_unique(b, acc);
        }
        MAnd(xs) | MOr(xs) => { for x in xs { collect_vars_unique(x, acc); } }
        True | False => {}
    }
}

fn join_ids_debug(b: &QcirBuilder, ids: &[usize]) -> String {
    ids.iter()
        .map(|&id| b.fmt_atom(id))   // use name if debug, else gN
        .collect::<Vec<_>>()
        .join(", ")
}
//
// ---------- Combined: unrolling + QCIR emission ----------
//


/// Unroll a vector of `transitions` against a vector of `(Quant, path)` prefixes.
/// - If lengths match, pairwise (transitions[i] with path_prefixes[i]).
/// - If one len is 1, broadcast it across the other.
/// - Else, error.
/// All headers (aggregated per path) are printed at the top; the unrolled body is in the middle.
pub fn to_qcir_unrolled(
    transitions: &[(Expression,Expression)],
    predicates_map: &HashMap<String, Expression>,
    path_prefixes: &[(Quant, String)], // e.g., &[(Forall,"A"), (Exists,"B")]
    formula_expr: &Expression,
    bound: usize,                    // i = 0..bound-1; primes use i+1
) -> Result<String, LowerError> {
    // Determine pairing strategy
    let (n_t, n_p) = (transitions.len(), path_prefixes.len());
    if n_t == 0 || n_p == 0 {
        // Vacuous: no body; just empty headers
        return to_qcir_string(&[], &[], &Expression::True, &[]);
    }
    let pair_count = match (n_t, n_p) {
        (t, p) if t == p => t,
        (1, p) => p,      // broadcast the single transition across all paths
        (t, 1) => t,      // broadcast the single path across all transitions
        _ => {
            return Err(LowerError::Temporal(
                "mismatched lengths: cannot pair transitions and path_prefixes",
            ));
        }
    };

    // For each pair, build its unrolled clause.
    let mut init_clauses: Vec<Expression> = Vec::with_capacity(pair_count);
    let mut body_clauses: Vec<Expression> = Vec::with_capacity(pair_count);

    // Also aggregate variables per path 
    // (so headers include all time-stamped vars used under that path)
    use std::collections::BTreeMap;
    let mut per_path_vars: BTreeMap<usize, Vec<Variable>> = BTreeMap::new(); 
    // key = path index in path_prefixes

    for i in 0..pair_count {
        // Select transition and (Quant, path) using broadcasting rules
        let t_idx = if n_t == 1 { 0 } else { i };
        let p_idx = if n_p == 1 { 0 } else { i };

        let (init, trans) = &transitions[t_idx];
        let (q, path) = &path_prefixes[p_idx];
        // let pred = &predicates[i].clone();

        // println!("trans: {:?}", expression_to_string(trans));
        // println!("preds: {:?}", expression_to_string(pred));
        // println!("init: {:?}", expression_to_string(&init_expr));
        
        // Unroll this transition on this path
        let init_expr = build_init_expr(init, &path);
        let clause = unroll_on_path_with_preds(trans, path, bound, &predicates_map);

        // Collect all variables and accumulate under this path index
        let mut vset: HashSet<Variable> = HashSet::new();
        collect_vars_unique(&init_expr, &mut vset);
        collect_vars_unique(&clause, &mut vset);
        // println!("(len={}):", vset.len());
        // for (i, item) in vset.iter().enumerate() {
        //         println!("  [{}] {:?}", i, item);
        // }

        // add them into the header list
        let vlist: Vec<Variable> = vset.into_iter().collect();
        let entry = per_path_vars.entry(p_idx).or_default();
        entry.extend(vlist);

        let clause_sub = subst_predicates_fixpoint(&clause, predicates_map);

        // Store the clause
        body_clauses.push(clause_sub);
        init_clauses.push(init_expr.clone());
        // init_clauses.push(pred.clone())
    }



    // Dedup/sort aggregated vars per path, and build the final header blocks
    let mut header_blocks: Vec<(Quant, Vec<Variable>)> = Vec::with_capacity(n_p);
    for (p_idx, (q, _path)) in path_prefixes.iter().enumerate() {
        let mut vars = per_path_vars
            .get(&p_idx)
            .cloned()
            .unwrap_or_default();
        vars.sort();
        vars.dedup();
        header_blocks.push((*q, vars));
    }

    // Emit a single QCIR: headers at the top; body = AND of all unrolled clauses
    to_qcir_string(&init_clauses, &body_clauses, &formula_expr, &header_blocks)
}



pub fn conjunct_formula_with_all_phi_pos(
    formula_expr: &Expression,
    all_phi_pos: &[(TrajQuant, Expression)],
) -> Expression {
    // Start with the main formula
    let mut parts: Vec<Box<Expression>> = vec![Box::new(formula_expr.clone())];

    // Append all φ_pos blocks (ignore the TrajQuant tag here)
    for (_, phi) in all_phi_pos {
        parts.push(Box::new(phi.clone()));
    }

    // Build a single conjunctive expression
    match parts.len() {
        0 => Expression::True, // shouldn't happen
        1 => *parts.pop().unwrap(),
        2 => {
            let r = parts.pop().unwrap();
            let l = parts.pop().unwrap();
            Expression::And(l, r)
        }
        _ => Expression::MAnd(parts),
    }
}

pub fn to_qcir_unrolled_ahltl(
    transitions: &[(Expression,Expression)],
    path_prefixes: &[(Quant, String)], // e.g., &[(Forall,"A"), (Exists,"B")]
    formula_expr: &Expression,
    predicates_map: &HashMap<String, Expression>,
    all_phi_pos: &[(TrajQuant, Expression)],
    bound: usize,                    // i = 0..bound-1; primes use i+1
) -> Result<String, LowerError> {
    // Determine pairing strategy
    let (n_t, n_p) = (transitions.len(), path_prefixes.len());
    if n_t == 0 || n_p == 0 {
        // Vacuous: no body; just empty headers
        return to_async_qcir_string(&[], &[], &Expression::True, &[],  &[]);
    }
    let pair_count = match (n_t, n_p) {
        (t, p) if t == p => t,
        (1, p) => p,      // broadcast the single transition across all paths
        (t, 1) => t,      // broadcast the single path across all transitions
        _ => {
            return Err(LowerError::Temporal(
                "mismatched lengths: cannot pair transitions and path_prefixes",
            ));
        }
    };

    // For each pair, build its unrolled clause.
    let mut init_clauses: Vec<Expression> = Vec::with_capacity(pair_count);
    let mut body_clauses: Vec<Expression> = Vec::with_capacity(pair_count);

    // Also aggregate variables per path 
    // (so headers include all time-stamped vars used under that path)
    use std::collections::BTreeMap;
    let mut per_path_vars: BTreeMap<usize, Vec<Variable>> = BTreeMap::new(); 
    // key = path index in path_prefixes

    for i in 0..pair_count {
        // Select transition and (Quant, path) using broadcasting rules
        let t_idx = if n_t == 1 { 0 } else { i };
        let p_idx = if n_p == 1 { 0 } else { i };

        let (init, trans) = &transitions[t_idx];
        let (q, path) = &path_prefixes[p_idx];
        // let pred = &predicates[i].clone();
        // Unroll this transition on this path
        let init_expr = build_init_expr(init, &path);
        let clause = unroll_on_path_with_preds(trans, path, bound, &predicates_map);

        // Collect all variables and accumulate under this path index
        let mut vset: HashSet<Variable> = HashSet::new();
        collect_vars_unique(&init_expr, &mut vset);
        collect_vars_unique(&clause, &mut vset);

        // add them into the header list
        let vlist: Vec<Variable> = vset.into_iter().collect();
        let entry = per_path_vars.entry(p_idx).or_default();
        entry.extend(vlist);

        let clause_sub = subst_predicates_fixpoint(&clause, predicates_map);

        // Store the clause
        body_clauses.push(clause_sub);
        init_clauses.push(init_expr.clone());
    }
    
    // Dedup/sort aggregated vars per path, and build the final header blocks
    let mut header_blocks: Vec<(Quant, Vec<Variable>)> = Vec::new();
    for (p_idx, (q, _path)) in path_prefixes.iter().enumerate() {
        let mut vars = per_path_vars
            .get(&p_idx)
            .cloned()
            .unwrap_or_default();
        vars.sort();
        vars.dedup();
        header_blocks.push((*q, vars));
    }

    let mut traj_prefixes: Vec<(Quant, Vec<Variable>)> = Vec::new();
    for (tq, expr) in all_phi_pos {
        // 1) Collect unique variables appearing in this expression
        let mut vset: HashSet<Variable> = HashSet::new();
        collect_vars_unique(expr, &mut vset);

        if vset.is_empty() {
            continue; // nothing to declare for this piece
        }

        // 2) Make a stable, sorted Vec<Variable>
        let mut vars: Vec<Variable> = vset.into_iter().collect();
        // If Variable implements Display or has a name getter, use that for sorting
        vars.sort_by(|a, b| a.to_string().cmp(&b.to_string()));

        // 3) Map trajectory quantifier → normal quantifier
        let q = match tq {
            TrajQuant::TrajA => Quant::Forall,
            TrajQuant::TrajE => Quant::Exists,
        };

        traj_prefixes.push((q, vars));
    }


    let final_formula = conjunct_formula_with_all_phi_pos(&formula_expr, &all_phi_pos);

    // Emit a single QCIR: headers at the top; body = AND of all unrolled clauses
    to_async_qcir_string(&init_clauses, &body_clauses, &final_formula, &header_blocks, &traj_prefixes)
}



























pub fn subst_predicates_fixpoint(e: &Expression, predmap: &std::collections::HashMap<String, Expression>) -> Expression {
    const MAX_ROUNDS: usize = 64; // safety cap for accidental cycles
    let mut cur = e.clone();
    for _ in 0..MAX_ROUNDS {
        let next = subst_predicates(&cur, predmap);
        if next == cur {
            return cur;
        }
        cur = next;
    }
    panic!("Predicate substitution did not converge (possible cyclic predicates).");
}

pub fn subst_predicates(e: &Expression, predmap: &PredMap) -> Expression {
    use Expression::*;
    use Lit::*;

    match e {
        Literal(Atom(name)) => {
            if let Some(body) = predmap.get(name) {
                body.clone()
            } else {
                e.clone()
            }
        }
        Literal(NegAtom(name)) => {
            if let Some(body) = predmap.get(name) {
                Neg(Box::new(body.clone()))
            } else {
                e.clone()
            }
        }

        True | False => e.clone(),
        Neg(x)       => Neg(Box::new(subst_predicates(x, predmap))),
        And(a,b)     => And(Box::new(subst_predicates(a, predmap)), Box::new(subst_predicates(b, predmap))),
        Or(a,b)      => Or(Box::new(subst_predicates(a, predmap)),  Box::new(subst_predicates(b, predmap))),
        Implies(a,b) => Implies(Box::new(subst_predicates(a, predmap)), Box::new(subst_predicates(b, predmap))),
        Iff(a,b)     => Iff(Box::new(subst_predicates(a, predmap)),     Box::new(subst_predicates(b, predmap))),
        MAnd(xs)     => MAnd(xs.iter().map(|x| Box::new(subst_predicates(x, predmap))).collect()),
        MOr(xs)      => MOr(xs.iter().map(|x| Box::new(subst_predicates(x, predmap))).collect()),
        _ => todo!(),
    }
}

/// Stamp an init expression with a path name and time = 0.
/// Every atom `x` becomes `x[PATH][0]`.
pub fn build_init_expr(expr: &Expression, path: &str) -> Expression {
    fn stamp(expr: &Expression, path: &str) -> Expression {
        use Expression::*;
        match expr {
            True | False => expr.clone(),

            Expression::Literal(Lit::Atom(v)) => {
                let new = format!("{}[{}][0]", v, path);
                Expression::Literal(Lit::Atom(new))
            }
            Expression::Literal(Lit::NegAtom(v)) => {
                let new = format!("{}[{}][0]", v, path);
                Expression::Literal(Lit::NegAtom(new))
            }

            Neg(x)       => Neg(Box::new(stamp(x, path))),
            And(a,b)     => And(Box::new(stamp(a, path)), Box::new(stamp(b, path))),
            Or(a,b)      => Or(Box::new(stamp(a, path)), Box::new(stamp(b, path))),
            MAnd(xs)     => MAnd(xs.iter().map(|x| Box::new(stamp(x, path))).collect()),
            MOr(xs)      => MOr(xs.iter().map(|x| Box::new(stamp(x, path))).collect()),
            Implies(a,b) => Implies(Box::new(stamp(a, path)), Box::new(stamp(b, path))),
            Iff(a,b)     => Iff(Box::new(stamp(a, path)), Box::new(stamp(b, path))),

            // We usually don’t expect temporal ops in init, but handle conservatively
            G(x) => G(Box::new(stamp(x, path))),
            F(x) => F(Box::new(stamp(x, path))),
            X(x) => X(Box::new(stamp(x, path))),
            U(a,b) => U(Box::new(stamp(a, path)), Box::new(stamp(b, path))),
            R(a,b) => R(Box::new(stamp(a, path)), Box::new(stamp(b, path))),
        }
    }
    stamp(expr, path)
}


// prefix: &[(Quant, Vec<Variable>)]
pub fn build_QBF(
    prefix: &[(Quant, Vec<Variable>)], 
    models: &[Expression], 
    formula: &Expression
) -> Option<Expression> {
    // append formula to the models list
    let mut all_models: Vec<Expression> = models.to_vec();
    all_models.push(formula.clone());

    let n = prefix.len().min(all_models.len());
    if n == 0 {
        return None;
    }

    let mut acc = all_models[n].clone();

    for i in (0..n).rev() {
        let (q, _vars) = &prefix[i];
        let m = all_models[i].clone();
        acc = match q {
            Quant::Forall => Expression::Implies(Box::new(m), Box::new(acc)),
            Quant::Exists => Expression::And(Box::new(m), Box::new(acc)),
        };
    }

    Some(acc)
}


/// Build an async-QBF-style formula by folding quantifier blocks for both
/// models and trajectories, then the final `formula`.
/// - `prefix`: quantifier blocks (Forall/Exists with their vars), order matters
/// - `model_blocks`: per-model constraints (one per path/model)
/// - `traj_blocks`: per-trajectory constraints (one per trajectory variable)
/// - `formula`: tail constraint
///
/// Result:
///   ∀/∃ m0 ⟹/∧ ( ∀/∃ m1 ⟹/∧ ( ... ( ∀/∃ t0 ⟹/∧ ( ... formula ) ) ... ) )
///
/// Notes:
/// - Uses implication for `Forall`, conjunction for `Exists` (as in your original).
/// - If lengths don’t match perfectly, we fold up to `min(prefix.len(), model_blocks.len()+traj_blocks.len())`.
// prefix: &[(Quant, Vec<Variable>)]
pub fn build_async_QBF(
    prefix: &[(Quant, Vec<Variable>)], 
    models: &[Expression], 
    formula: &Expression,
    pos_prefix: &[(Quant, Vec<Variable>)],
) -> Option<Expression> {
    // append formula to the models list
    let mut acc = formula.clone();

    // Total number of “blocks” available to pair with prefix:
    //   - one per model
    //   - one per extra ∃-block in pos_prefix (these have no expression => use True)
    let total_blocks = models.len();

    // We can only fold as many prefix entries as we have blocks.
    let usable = prefix.len().min(total_blocks);
    if usable == 0 {
        return Some(acc);
    }

    // Fold from right to left
    for i in (0..usable).rev() {
        // Pick the block expression:
        //   - if it's within models, use the model expression
        //   - otherwise, it corresponds to an extra ∃-block in pos_prefix: use True
        let m = if i < models.len() {
            models[i].clone()
        } else {
            Expression::True
        };

        let (q, _vars) = &prefix[i];
        acc = match q {
            Quant::Forall => Expression::Implies(Box::new(m), Box::new(acc)),
            Quant::Exists => Expression::And(Box::new(m), Box::new(acc)),
        };
    }

    Some(acc)
}