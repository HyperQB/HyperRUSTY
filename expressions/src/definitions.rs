use std::mem;
// ***************** Definitions *****************
#[derive(Debug)]
pub enum Error {
    ErrorInNNF,
    ErrorMergingLets,
}


#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Quant { Forall, Exists}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrajQuant { TrajA, TrajE }

impl Quant {
    pub fn as_str(self) -> &'static str {
        match self {
            Quant::Forall => "forall",
            Quant::Exists => "exists",
        }
    }

    /// Convert a &str into a Quant. Returns None if not recognized.
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "Forall" | "forall" => Some(Quant::Forall),
            "Exists" | "exists" => Some(Quant::Exists),
            _ => None,
        }
    }
}

impl TrajQuant {
    pub fn as_str(self) -> &'static str {
        match self {
            TrajQuant::TrajA => "A",
            TrajQuant::TrajE => "E",
        }
    }

    /// Convert a &str into a Quant. Returns None if not recognized.
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "A" => Some(TrajQuant::TrajA),
            "E" => Some(TrajQuant::TrajE),
            _ => None,
        }
    }
}



pub type Variable = String; /// A variable is a string.
pub type Ident = String;

// We use Box here. https://doc.rust-lang.org/std/boxed/index.html
// It is a smart pointer with the ability to allocate memory on the heap.
#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub enum Literal {
    /// An atom is a variable that can be true or false.
    Atom(Variable),
    NegAtom(Variable),
}

#[derive(Debug, Eq, PartialEq, Clone, Hash, Default)]
/// An expression is a logical statement that can be true or false.
pub enum Expression {
    #[default]
    True,
    False,
    Literal(Literal),
    Neg(Box<Expression>),
    Or(Box<Expression>, Box<Expression>),
    MOr(Vec<Box<Expression>>),
    And(Box<Expression>, Box<Expression>),
    MAnd(Vec<Box<Expression>>),
    Implies(Box<Expression>, Box<Expression>),
    Iff(Box<Expression>, Box<Expression>),
    G(Box<Expression>),
    F(Box<Expression>),
    X(Box<Expression>),
    U(Box<Expression>, Box<Expression>),
    R(Box<Expression>, Box<Expression>)
}

/// Drop the expression in a non-recursive way
pub fn drop_expression(expression: Expression) {
    let mut stack = vec![expression];

    while let Some(mut current) = stack.pop() {
        match &mut current {
            Expression::Neg(inner)
            | Expression::G(inner)
            | Expression::F(inner)
            | Expression::X(inner) => {
                stack.push(mem::take(inner));
            }
            Expression::And(left, right)
            | Expression::Or(left, right)
            | Expression::Implies(left, right)
            | Expression::Iff(left, right)
            | Expression::U(left, right)
            | Expression::R(left, right) => {
                stack.push(mem::take(left));
                stack.push(mem::take(right));
            }
            Expression::MOr(inner) | Expression::MAnd(inner) => {
                for expr in mem::take(inner) {
                    stack.push(*expr);
                }
            }
            _ => {}
        }
    }
}

pub type LetClause = (Ident, Expression);

#[derive(Debug, Eq, PartialEq, Clone)]
/// A DisjunctiveFormula is a logical statement that is true if any of its literals are true.
pub enum DisjunctiveFormula {
    FalseDisj,
    TrueDisj,
    Disj(Vec<Literal>),
}

#[derive(Debug, Eq, PartialEq, Clone)]
/// A ConjunctiveFormula is a logical statement that is true if all of its literals are true.
pub enum ConjunctiveFormula {
    FalseConj,
    TrueConj,
    Conj(Vec<Literal>),
}

#[derive(Debug, Eq, PartialEq, Clone)]
/// A Formula is a logical statement that can be true or false.
pub enum Formula {
    Let(Ident, Box<Expression>, Box<Formula>),
    CNF(Vec<DisjunctiveFormula>),
    DNF(Vec<ConjunctiveFormula>),
    General(Box<Expression>),
    ConjF(Vec<Formula>),
    DisjF(Vec<Formula>),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Quantifier {
    Forall(Vec<Variable>),
    Exists(Vec<Variable>),
}

pub type QuantifiedExpression = (Vec<Quantifier>, Box<Expression>);

pub type QuantifiedFormula = (Vec<Quantifier>, Formula);

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum LogicOpT {
    AndOp,
    OrOp,
    ImpliesOp,
    IffOp,
    NegOp,
    NoneOp,
    LetOp,
}

pub const TRUE_SYM:         &str = "TRUE";
pub const FALSE_SYM:        &str = "FALSE";
pub const AND_SYM:          &str = "&";
pub const OR_SYM:           &str = "|";
pub const NEG_SYM:          &str = "~";
pub const IMPL_SYM:         &str = "->";  // becomes not(expr1) \/ expr2
pub const IFF_SYM:          &str = "<->"; // becomes (expr1 -> expr2) /\ (expr2 -> expr1)
pub const LET_SYM:          &str = "let";
pub const GLOBAL_CHECK:     &str = "\\bG\\b";
pub const EVENTUALLY_CHECK: &str = "\\bF\\b";
pub const UNTIL_CHECK:      &str = "\\bU\\b";
pub const NEXT_CHECK:       &str = "\\bX\\b";
pub const RELEASE_CHECK:    &str = "\\bR\\b";
pub const GLOBAL:           &str = "G";
pub const EVENTUALLY:       &str = "F";
pub const UNTIL:            &str = "U";
pub const NEXT:             &str = "X";
pub const RELEASE:          &str = "R";
pub const TEMPORAL_SET: [&str; 5] = [GLOBAL, EVENTUALLY, UNTIL, NEXT, RELEASE];

