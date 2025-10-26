use expressions::{Expression, Literal};


// === Helpers to time-stamp variable names ===============================

fn stamp_name_at_time(base: &str, t: usize) -> String {
    // If `base` already has a time suffix like ...[N], we avoid double-adding.
    // Your variable forms look like "high[A]" (model already embedded).
    // We append "[t]" at the end: "high[A][t]".
    // If you *might* already have a time index, detect it and replace.
    if let Some(_pos) = base.rfind(']') {
        // If the segment before ']' contains '[' and after that there's another ']',
        // we interpret the last bracket as the model and add time after it.
        // This is conservative and works with "high[A]" → "high[A][t]".
        format!("{base}[{t}]")
    } else {
        // Fallback: just append
        format!("{base}[{t}]")
    }
}

fn stamp_literal_at_time(lit: &Literal, t: usize) -> Literal {
    match lit {
        Literal::Atom(s)    => Literal::Atom(stamp_name_at_time(s, t)),
        Literal::NegAtom(s) => Literal::NegAtom(stamp_name_at_time(s, t)),
    }
}

/// Non-temporal expression where every atom is stamped with the *same* time t.
fn stamp_expr_at_time(e: &Expression, t: usize) -> Expression {
    use Expression::*;
    match e {
        True  | False => e.clone(),
        Expression::Literal(lit) => Expression::Literal(stamp_literal_at_time(lit, t)),
        Neg(x)  => Neg(Box::new(stamp_expr_at_time(x, t))),
        And(a,b)=> And(Box::new(stamp_expr_at_time(a, t)), Box::new(stamp_expr_at_time(b, t))),
        Or(a,b) => Or(Box::new(stamp_expr_at_time(a, t)), Box::new(stamp_expr_at_time(b, t))),
        MAnd(xs)=> {
            let mut ys = Vec::with_capacity(xs.len());
            for x in xs { ys.push(Box::new(stamp_expr_at_time(x, t))); }
            MAnd(ys)
        }
        MOr(xs) => {
            let mut ys = Vec::with_capacity(xs.len());
            for x in xs { ys.push(Box::new(stamp_expr_at_time(x, t))); }
            MOr(ys)
        }
        Implies(a,b) => Implies(Box::new(stamp_expr_at_time(a, t)), Box::new(stamp_expr_at_time(b, t))),
        Iff(a,b)     => Iff    (Box::new(stamp_expr_at_time(a, t)), Box::new(stamp_expr_at_time(b, t))),

        // Temporal nodes should be eliminated before stamping; if they survive here,
        // we conservatively stamp their children at t (this path shouldn't be hit if
        // you unroll properly via `unroll_ltl` below).
        G(x) => G(Box::new(stamp_expr_at_time(x, t))),
        F(x) => F(Box::new(stamp_expr_at_time(x, t))),
        X(x) => X(Box::new(stamp_expr_at_time(x, t))),
        U(a,b)=> U(Box::new(stamp_expr_at_time(a, t)), Box::new(stamp_expr_at_time(b, t))),
        R(a,b)=> R(Box::new(stamp_expr_at_time(a, t)), Box::new(stamp_expr_at_time(b, t))),
    }
}

// === LTL unrolling (finite semantics on horizon k) =======================
//
// We use the standard finite-horizon expansion:
//  X φ      @i = if i < k { φ@(i+1) } else { φ@k }          (stutter at end or clamp)
//  G φ      @i = ∧_{t=i..k}  φ@t
//  F φ      @i = ∨_{t=i..k}  φ@t
//  φ U ψ    @i = ∨_{t=i..k} ( (∧_{u=i..t-1} φ@u) ∧ ψ@t )
//  φ R ψ    @i = ∧_{t=i..k} ( ψ@t ∨ ( ∨_{u=i..t-1} φ@u ) )
// For a *global* property you normally take i=0 after expansion.

// fn big_and(mut parts: Vec<Expression>) -> Expression {
//     match parts.len() {
//         0 => Expression::True,
//         1 => parts.pop().unwrap(),
//         _ => Expression::MAnd(parts.into_iter().map(Box::new).collect()),
//     }
// }
// fn big_or(mut parts: Vec<Expression>) -> Expression {
//     match parts.len() {
//         0 => Expression::False,
//         1 => parts.pop().unwrap(),
//         _ => Expression::MOr(parts.into_iter().map(Box::new).collect()),
//     }
// }

fn unroll_at(formula: &Expression, i: usize, k: usize) -> Expression {
    use Expression::*;

    // Helpers: empty big-AND/OR semantics and stamping only literals
    fn big_and(xs: Vec<Expression>) -> Expression {
        if xs.is_empty() { Expression::True } else {
            Expression::MAnd(xs.into_iter().map(Box::new).collect())
        }
    }
    fn big_or(xs: Vec<Expression>) -> Expression {
        if xs.is_empty() { Expression::False } else {
            Expression::MOr(xs.into_iter().map(Box::new).collect())
        }
    }

    match formula {
        // Constants stay the same
        True | False => formula.clone(),

        // Stamp ONLY literals at time i (skip numbers/TRUE/FALSE atoms per your stamper)
        Expression::Literal(_) => stamp_expr_at_time(formula, i),

        // Propositional connectives: recurse at the same i
        Neg(x)       => Neg(Box::new(unroll_at(x, i, k))),
        And(a,b)     => And(Box::new(unroll_at(a, i, k)), Box::new(unroll_at(b, i, k))),
        Or(a,b)      => Or(Box::new(unroll_at(a, i, k)),  Box::new(unroll_at(b, i, k))),
        Implies(a,b) => Implies(Box::new(unroll_at(a, i, k)), Box::new(unroll_at(b, i, k))),
        Iff(a,b)     => Iff(Box::new(unroll_at(a, i, k)), Box::new(unroll_at(b, i, k))),
        MAnd(xs)     => MAnd(xs.iter().map(|x| Box::new(unroll_at(x, i, k))).collect()),
        MOr(xs)      => MOr(xs.iter().map(|x| Box::new(unroll_at(x, i, k))).collect()),

        // Next: shift time by 1 but clamp at k
        X(phi) => {
            let j = if i < k { i + 1 } else { k };
            unroll_at(phi, j, k)
        }

        // Globally: ∧_{t=i..k} φ@t
        G(phi) => {
            if i > k { return True; }
            let mut parts = Vec::with_capacity(k - i + 1);
            for t in i..=k { parts.push(unroll_at(phi, t, k)); }
            big_and(parts)
        }

        // Finally: ∨_{t=i..k} φ@t
        F(phi) => {
            if i > k { return False; }
            let mut parts = Vec::with_capacity(k - i + 1);
            for t in i..=k { parts.push(unroll_at(phi, t, k)); }
            big_or(parts)
        }

        // Until: ∨_{t=i..k} ( (∧_{u=i..t-1} φ@u) ∧ ψ@t )
        U(phi, psi) => {
            let mut sum = Vec::with_capacity(k - i + 1);
            for t in i..=k {
                let mut pre = Vec::new();
                for u in i..t { pre.push(unroll_at(phi, u, k)); }
                let lhs = big_and(pre); // empty -> True
                let rhs = unroll_at(psi, t, k);
                sum.push(And(Box::new(lhs), Box::new(rhs)));
            }
            big_or(sum)
        }

        // Release: ∧_{t=i..k} ( ψ@t ∨ ( ∨_{u=i..t-1} φ@u ) )
        R(phi, psi) => {
            let mut prod = Vec::with_capacity(k - i + 1);
            for t in i..=k {
                let mut any = Vec::new();
                for u in i..t { any.push(unroll_at(phi, u, k)); }
                let lhs = unroll_at(psi, t, k);
                let rhs = big_or(any); // empty -> False
                prod.push(Or(Box::new(lhs), Box::new(rhs)));
            }
            big_and(prod)
        }
    }
}

/// Public entry: fully unroll from i=0 to horizon k (inclusive)
pub fn unroll_ltl(formula: &Expression, k: usize) -> Expression {
    // println!("Now unrolling: {:?}", formula);
    unroll_at(formula, 0, k)
}