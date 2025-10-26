use std::collections::HashMap;
use z3::ast::{Ast, Bool};
use crate::Expression;
use crate::Literal;



/// Parse an inner LTL formula into `Expression`.
/// Supported:
///   atoms: [A-Za-z_][A-Za-z0-9_\[\]]*
///   consts: true / false   (mapped to Atom("true") / NegAtom("true"))
///   unary:  !  G  F  X
///   binary: U  R  &  |  ->  <->   (with the usual precedences)
///   parens: ( ... )
pub fn parse_inner_ltl(input: &str) -> Expression {
    let mut p = Parser::new(input);
    let expr = p.parse_equiv().expect("parse error"); // start at lowest precedence (<->)
    p.skip_ws();
    if !p.eof() {
        panic!("unexpected trailing input at pos {}", p.i);
    }
    expr
}

struct Parser<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> Parser<'a> {
    fn new(s: &'a str) -> Self { Self { s: s.as_bytes(), i: 0 } }
    fn eof(&self) -> bool { self.i >= self.s.len() }
    fn peek(&self) -> Option<u8> { self.s.get(self.i).copied() }
    // fn bump(&mut self) -> Option<u8> {
    //     if self.eof() { None } else { let c = self.s[self.i]; self.i += 1; Some(c) }
    // }
    fn skip_ws(&mut self) { while matches!(self.peek(), Some(b' ' | b'\t' | b'\n' | b'\r')) { self.i += 1; } }

    // ---------- lexical helpers ----------
    fn starts_ident_byte(b: u8) -> bool { b.is_ascii_alphabetic() || b == b'_' }
    fn is_ident_byte(b: u8) -> bool { b.is_ascii_alphanumeric() || matches!(b, b'_' | b'[' | b']') }

    fn parse_ident(&mut self) -> Option<String> {
        self.skip_ws();
        let start = self.i;
        if !self.peek().map_or(false, Self::starts_ident_byte) { return None; }
        self.i += 1;
        while let Some(b) = self.peek() {
            if Self::is_ident_byte(b) { self.i += 1; } else { break; }
        }
        Some(String::from_utf8(self.s[start..self.i].to_vec()).unwrap())
    }

    fn eat(&mut self, tok: &str) -> bool {
        self.skip_ws();
        let bytes = tok.as_bytes();
        if self.i + bytes.len() <= self.s.len() && &self.s[self.i..self.i + bytes.len()] == bytes {
            self.i += bytes.len();
            true
        } else { false }
    }

    // ---------- precedence climbing ----------
    // equiv (<->)
    fn parse_equiv(&mut self) -> Result<Expression, String> {
        let mut left = self.parse_implies()?;
        loop {
            self.skip_ws();
            if self.eat("<->") {
                let right = self.parse_implies()?;
                left = Expression::Iff(Box::new(left), Box::new(right));
            } else { break; }
        }
        Ok(left)
    }

    // implies (->)
    fn parse_implies(&mut self) -> Result<Expression, String> {
        let mut left = self.parse_or()?;
        loop {
            self.skip_ws();
            if self.eat("->") {
                let right = self.parse_or()?;
                left = Expression::Implies(Box::new(left), Box::new(right));
            } else { break; }
        }
        Ok(left)
    }

    // or (|)
    fn parse_or(&mut self) -> Result<Expression, String> {
        let mut parts = vec![ self.parse_and()? ];
        loop {
            self.skip_ws();
            if self.peek() == Some(b'|') { self.i += 1; parts.push(self.parse_and()?); }
            else { break; }
        }
        Ok(match parts.len() {
            1 => parts.pop().unwrap(),
            _ => Expression::MOr(parts.into_iter().map(Box::new).collect())
        })
    }

    // and (&)
    fn parse_and(&mut self) -> Result<Expression, String> {
        let mut parts = vec![ self.parse_ur()? ];
        loop {
            self.skip_ws();
            if self.peek() == Some(b'&') { self.i += 1; parts.push(self.parse_ur()?); }
            else { break; }
        }
        Ok(match parts.len() {
            1 => parts.pop().unwrap(),
            _ => Expression::MAnd(parts.into_iter().map(Box::new).collect())
        })
    }

    // until / release (U / R)
    fn parse_ur(&mut self) -> Result<Expression, String> {
        let mut left = self.parse_unary()?;
        loop {
            self.skip_ws();
            if self.eat("U") {
                let right = self.parse_unary()?;
                left = Expression::U(Box::new(left), Box::new(right));
            } else if self.eat("R") {
                let right = self.parse_unary()?;
                left = Expression::R(Box::new(left), Box::new(right));
            } else { break; }
        }
        Ok(left)
    }

    // unary: !, G, F, X, primary
    fn parse_unary(&mut self) -> Result<Expression, String> {
        self.skip_ws();
        if self.eat("!") { return Ok(Expression::Neg(Box::new(self.parse_unary()?))); }
        if self.eat("G") { return Ok(Expression::G  (Box::new(self.parse_unary()?))); }
        if self.eat("F") { return Ok(Expression::F  (Box::new(self.parse_unary()?))); }
        if self.eat("X") { return Ok(Expression::X  (Box::new(self.parse_unary()?))); }
        self.parse_primary()
    }

    // primary: ( ... )  |  true/false/ident
    fn parse_primary(&mut self) -> Result<Expression, String> {
        self.skip_ws();
        if self.peek() == Some(b'(') {
            self.i += 1;
            let e = self.parse_equiv()?;
            self.skip_ws();
            if self.peek() != Some(b')') {
                return Err(format!("expected ')' at pos {}", self.i));
            }
            self.i += 1;
            return Ok(e);
        }
        if let Some(ident) = self.parse_ident() {
            // Map "true"/"false" to Atom("true") / NegAtom("true")
            if ident.eq_ignore_ascii_case("true") {
                return Ok(Expression::Literal(Literal::Atom("true".to_string())));
            } else if ident.eq_ignore_ascii_case("false") {
                return Ok(Expression::Literal(Literal::NegAtom("true".to_string())));
            } else {
                return Ok(Expression::Literal(Literal::Atom(ident)));
            }
        }
        Err(format!("unexpected token at pos {}", self.i))
    }
}


// The next two functions are used to generate the expression for the initial states if using new smv
// We do this because the legacy and encoding unroll are already built and tested. It is easier to adjust input
// to fit into them then to rewrite the smv unroll.
pub fn build_expression(variable_map: &HashMap<String, Vec<String>>) -> String {
    // Collect variables and their values
    let variables: Vec<(&String, &Vec<String>)> = variable_map.iter().collect();

    // Build expressions for each variable
    let mut expr_parts = Vec::new();
    for (var, values) in variables {
        if values.len() == 1 && values[0] == "TRUE" {
            // If the value is "TRUE", the variable itself is true
            expr_parts.push(var.clone());
        } else {
            // For each value, append it to the variable name
            let appended_vars: Vec<String> = values
                .iter()
                .map(|value| format!("{}[{}]", var, value))
                .collect();
            // Combine the appended variables using conjunction (/\\)
            let combined_expr = appended_vars.join("/\\");
            expr_parts.push(combined_expr);
        }
    }

    // Combine all variable expressions using conjunction (/\\)
    let expression = format!("({})", expr_parts.join("/\\"));

    expression
}


pub fn generate_combinations(
    variables: &Vec<(&String, &Vec<String>)>,
    index: usize,
    current: Vec<(String, String)>,
) -> Vec<Vec<(String, String)>> {
    if index == variables.len() {
        return vec![current];
    }

    let mut combinations = Vec::new();
    let (var, values) = variables[index];

    for value in values {
        let mut next = current.clone();
        let val_expr = match value.as_str() {
            "TRUE" | "1" => var.clone(),
            "FALSE" | "0" => format!("~{}", var),
            _ => format!("{}={}", var, value),
        };
        next.push((var.clone(), val_expr));
        combinations.extend(generate_combinations(variables, index + 1, next));
    }

    combinations
}

pub fn expr_to_string(expr: &Expression) -> String {
    match expr {
        Expression::Literal(s) => match s {
            Literal::Atom(s) => s.clone(),
            Literal::NegAtom(s) => format!("~{}", s),
        },
        Expression::Neg(e) => format!("~{}", expr_to_string(e)),
        Expression::MAnd(exprs) => {
            let parts: Vec<String> = exprs.iter().map(|e| expr_to_string(e)).collect();
            format!("({})", parts.join("/\\"))
        }
        Expression::MOr(exprs) => {
            let parts: Vec<String> = exprs.iter().map(|e| expr_to_string(e)).collect();
            format!("({})", parts.join("\\/"))
        }
        Expression::Or(left, right) => {
            format!("({} \\/ {})", expr_to_string(left), expr_to_string(right))
        }
        Expression::And(left, right) => {
            format!("({} /\\ {})", expr_to_string(left), expr_to_string(right))
        }
        _ => {println!("Error: {:?}", expr); panic!("Invalid expression type")}

    }
}

pub fn blast_bits(var_name: &str, state_num: i32, max_b: i32, bracket: &str) -> Vec<String> {
    let mut bit_order = 0;
    let mut max_bit_order = 0;
    let mut bit_vector: Vec<String> = Vec::new();
    let mut bit = String::new();
    let mut max_bit = String::new();
    let mut state = state_num.clone();
    let mut max = max_b.clone();
    
    while state != 0 {
        let r = if state % 2 == 0 { "0" } else { "1" };
        let var = format!("{}_{}_{}", var_name, bit_order, bracket);
        if r == "0" {
            bit_vector.push(format!("~{}", var));
        } else {
            bit_vector.push(var);
        }
        bit = format!("{}{}", r, bit);
        state /= 2;
        bit_order += 1;
        // println!("1");
    }
    
    while max != 0 {
        let max_r = if max % 2 == 0 { "0" } else { "1" };
        max_bit = format!("{}{}", max_r, max_bit);
        max /= 2;
        max_bit_order += 1;
        // println!("2");
    }
    
    while max_bit_order != bit_order {
        let var = format!("{}_{}_{}", var_name, bit_order, bracket);
        bit_vector.push(format!("~{}", var));
        bit_order += 1;
        // println!("3");
    }

    return bit_vector;
}

pub fn manipulate_pattern(max_bit: i32, var1: &str, bracket1: &str, rhs: &str, bracket2: Option<&str>) -> String {
    // if pattern is var = var
    if let Some(br) = bracket2 {
        
        // let combined_bit_vec: Vec<String> = Vec::new();

        // for i in 0..=max_bit {
        //     let bit_vec_1 = blast_bits(var1, i, max_bit, bracket1);
        //     let bit_vec_2 = blast_bits(rhs, i, max_bit, br);

        //     // combine 0 <-> 0 , 1 <-> 1, ...
        // }

        let bit_vec_1 = blast_bits(var1, max_bit, max_bit, bracket1);
        let bit_vec_2 = blast_bits(rhs, max_bit, max_bit, br);

        let final_formula = bit_vec_1.iter()
            .zip(bit_vec_2.iter())
            .map(|(a, b)| format!("{} <-> {}", a, b))
            .collect::<Vec<_>>()
            .join(" /\\ ");

        return final_formula

        // format!("{}[{}] = {}[{}]", var1, bracket1, rhs, br)

    // if pattern is var = int
    } else {
        let state_num: i32 = rhs.parse().expect("REASON");
        let bit_vec = blast_bits(var1, state_num, max_bit, bracket1);
        let final_formula = bit_vec.join(" /\\ ");
        return final_formula

        // format!("{}[{}] = {}", var1, bracket1, rhs)
    }
}


pub fn expression_to_string(expr: &Expression) -> String {
    use crate::Expression::*;
    use crate::Literal::*;
    match expr {
        True => "true".to_string(),
        False => "false".to_string(),
        Literal(Atom(var)) => var.clone(),
        Literal(NegAtom(var)) => format!("~{}", var),
        Neg(inner) => format!("~({})", expression_to_string(inner)),
        And(left, right) => format!("({} & {})", expression_to_string(left), expression_to_string(right)),
        Or(left, right) => format!("({} | {})", expression_to_string(left), expression_to_string(right)),
        MAnd(inner) => {
            let parts: Vec<String> = inner.iter().map(|e| expression_to_string(e)).collect();
            format!("({})", parts.join(" & "))
        }
        MOr(inner) => {
            let parts: Vec<String> = inner.iter().map(|e| expression_to_string(e)).collect();
            format!("({})", parts.join(" | "))
        }
        Implies(a, b) => format!("({} -> {})", expression_to_string(a), expression_to_string(b)),
        Iff(a, b) => format!("({} <-> {})", expression_to_string(a), expression_to_string(b)),
        G(inner) => format!("G({})", expression_to_string(inner)),
        F(inner) => format!("F({})", expression_to_string(inner)),
        X(inner) => format!("X({})", expression_to_string(inner)),
        U(a, b) => format!("({}) U ({})", expression_to_string(a), expression_to_string(b)),
        R(a, b) => format!("({}) R ({})", expression_to_string(a), expression_to_string(b)),
    }
}

pub fn ir_to_initial_conditions(expr: &Bool) -> (String, Expression) {
    fn helper(expr: &Bool) -> (Option<String>, Expression) {
        let name = expr.decl().name();
        let op = name.as_str();

        match op {
            "true"  => (None, Expression::True),
            "false" => (None, Expression::False),

            "not" => {
                let arg = expr.children()[0].as_bool().unwrap();
                let (var, subexpr) = helper(&arg);
                (var, Expression::Neg(Box::new(subexpr)))
            }

            "and" => {
                let mut vars = None;
                let args = expr
                    .children()
                    .into_iter()
                    .map(|child| {
                        let bool_child = child.as_bool().unwrap();
                        let (var, ex) = helper(&bool_child);
                        if vars.is_none() && matches_var_0(&var) {
                            vars = var;
                        }
                        Box::new(ex)
                    })
                    .collect();
                (vars, Expression::MAnd(args))
            }

            "or" => {
                let mut vars = None;
                let args = expr
                    .children()
                    .into_iter()
                    .map(|child| {
                        let bool_child = child.as_bool().unwrap();
                        let (var, ex) = helper(&bool_child);
                        if vars.is_none() && matches_var_0(&var) {
                            vars = var;
                        }
                        Box::new(ex)
                    })
                    .collect();
                (vars, Expression::MOr(args))
            }

            "=" => {
                let lhs = expr.children()[0].to_string();
                let rhs = expr.children()[1].to_string();

                let varname = if lhs.ends_with("_0") {
                    Some(lhs.trim_end_matches("_0").to_string())
                } else {
                    None
                };

                let expr = match rhs.as_str() {
                    "true" => Expression::Literal(Literal::Atom(varname.clone().unwrap_or(lhs))),
                    "false" => Expression::Literal(Literal::NegAtom(varname.clone().unwrap_or(lhs))),
                    _ => Expression::Literal(Literal::Atom(format!("{}={}", varname.clone().unwrap_or(lhs), rhs))),
                };

                (varname, expr)
            }

            _ => {
                let atom = expr.to_string();
                let var = if atom.ends_with("_0") {
                    Some(atom.trim_end_matches("_0").to_string())
                } else {
                    None
                };
                (var.clone(), Expression::Literal(Literal::Atom(atom)))
            }
        }
    }

    fn matches_var_0(opt: &Option<String>) -> bool {
        match opt {
            Some(s) => s.ends_with("_0"),
            None => false,
        }
    }

    let (var, expr) = helper(expr);
    (var.unwrap_or_else(|| "unknown".to_string()), expr)
}

