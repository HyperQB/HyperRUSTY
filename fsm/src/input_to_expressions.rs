use expressions::*;
use regex::{CaptureMatches, Regex};
use stacker;
use crate::SymbolMap;

/// This is a helper function that will matches single variable tokens from the stack
fn single_expression_token_match(stack: &mut Vec<Box<Expression>>, token: &str){
    // match the token
    let state = stack.pop().unwrap();
    match token{
        GLOBAL => {
            stack.push(Box::new(Expression::G(state)));
        }
        EVENTUALLY => {
            stack.push(Box::new(Expression::F(state)));
        }
        NEG_SYM => {
            stack.push(Box::new(Expression::Neg(state)));
        }
        "(" => {
            stack.push(state);
        }
        _ => {unreachable!("Should not have gotten here");}
    }
}

fn format_literal(literal: &mut str, symbol_map: &mut SymbolMap, max_gate_number: &mut i32) -> String{
    // check if literal has "'"
    let mut is_prime = false;
    let mut return_val = literal.to_string();
    if literal.contains("'") {
        is_prime = true;
        return_val = return_val.replace("'", "");
    }
    if let Some(&_gate_number) = symbol_map.get(&(return_val.to_string()+"_0")) {
        // do nothing
    } else{
        //println!("Adding to symbol map: {}", return_val);
        symbol_map.insert(return_val.to_string(),max_gate_number);
        symbol_map.insert_helper(return_val.to_string(), max_gate_number);
    }
    return_val = return_val.to_string() + "_helper";
    if is_prime{
        return_val = return_val + "'";
    }
    return return_val


}


/// This function will take the expression and return the CDF form of the expression
pub fn input_to_expression(expression: &str) -> Box<Expression> {
    // Build the regex pattern dynamically
    // set time
    let pattern = r"~([^)(/]+)";
    let re = Regex::new(&pattern).unwrap();
    // Split the input on `->`
    let parts: Vec<&str> = expression.split("->").collect();

    // Perform the replacement on each part
    let replaced_parts: Vec<String> = parts.iter()
        .map(|part| re.replace_all(part, "(~$1)").to_string())
        .collect();

    // Join the parts back together with `->`
    let result = replaced_parts.join("->");

    // let binding = cow.to_string();
    // let mut results = binding.as_str();
    // Get out the regex
    let re = Regex::new(&format!(
        "({}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|\\(|\\)|\\d+(?:-\\d+)*|[a-zA-Z'_0-9\\[\\]]+(?:-[a-zA-Z'_0-9\\[\\]]+)*|-)",
        regex::escape(AND_SYM),
        regex::escape(OR_SYM),
        TRUE_SYM,
        FALSE_SYM,
        NEG_SYM,
        IMPL_SYM,
        IFF_SYM,
        regex::escape(GLOBAL_CHECK),
        regex::escape(EVENTUALLY_CHECK),
        regex::escape(UNTIL_CHECK),
        regex::escape(RELEASE_CHECK)
    )).unwrap();
    let mut captures = re.captures_iter(result.as_str());
    let mut stack: Vec<Box<Expression>> = Vec::new();
    let mut output: Vec<Box<Expression>> = Vec::new();

    /// This function will recurse down and pull out the CDF from the expression
    /// It will then return the result of the recursion where each and is a transition to be added to the fsm
    fn recurse_down(captures: &mut CaptureMatches, stack: &mut Vec<Box<Expression>>, output: &mut Vec<Box<Expression>>, pushed_break : bool, top_layer: bool) {
        stacker::maybe_grow(32*1024,1024*1024, || {
            while let Some(cap) = captures.next() {
                let token = cap.get(1).unwrap().as_str();
                match token {
                    TRUE_SYM => {
                        stack.push(Box::new(Expression::True));
                    }
                    FALSE_SYM => {
                        stack.push(Box::new(Expression::False));
                    }
                    // Only one expression inside of it
                    NEG_SYM | GLOBAL | EVENTUALLY => {
                        let mut breaking = false;
                        let next_token = captures.next().unwrap().get(1).unwrap().as_str();
                        // do we recurse or not
                        if (next_token == "(") | (next_token == GLOBAL) | (next_token == EVENTUALLY) {
                            recurse_down(captures, stack, output, pushed_break, false);
                            if next_token != "(" { // We break if we are recursing with anything other than (
                                breaking = true;
                            }
                        } else {
                            stack.push(Box::new(Expression::Literal(Literal::Atom(next_token.to_string()))));
                        }
                        // match the token
                        single_expression_token_match(stack, token);
                        // If we recursed then break
                        if breaking & !top_layer {
                            break;
                        }
                    }
                    // Two expressions inside of it
                    AND_SYM | OR_SYM | IMPL_SYM | IFF_SYM | UNTIL | RELEASE => {
                        let mut breaking = false;
                        let state = stack.pop().unwrap(); // left
                        let next_token = captures.next().unwrap().get(1).unwrap().as_str();
                        if next_token.contains("(") | (next_token == GLOBAL) | (next_token == EVENTUALLY) | (next_token == NEG_SYM){
                            if next_token == NEG_SYM {
                                recurse_down(captures, stack, output, true, false);
                            } else{
                                recurse_down(captures, stack, output, pushed_break, false);
                            }
                            // Deal with next states
                            single_expression_token_match(stack, next_token);
                            if next_token != "("  { // We break if we are recursing with anything other than (
                                breaking = true;
                            }
                        }
                        else {
                            stack.push(Box::new(Expression::Literal(Literal::Atom(next_token.to_string()))));
                        }
                        // if it was orignally matched with AND_SYM
                        match token {
                            AND_SYM => {
                                let next_state = stack.pop().unwrap(); // right

                                // Check if we can do a MAnd
                                if let Expression::MAnd(mut inner) = *state{ // left lets Mand
                                    if let Expression::MAnd(mut inner2) = *next_state{ // right lets Mand
                                        inner.append(&mut inner2);
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    } else if let Expression::And(left2,right2) = *next_state { // just left is Mand, but right is and
                                        inner.push(left2);
                                        inner.push(right2);
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    } else { // just left is Mand, right is not Mand or And
                                        inner.push(next_state);
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    }
                                } else if let Expression::And(left,right) = *state{
                                    if let Expression::MAnd(mut inner) = *next_state{ // left is and, right is Mand
                                        inner.push(left);
                                        inner.push(right);
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    } else if let Expression::And(left2,right2) = *next_state { // left is and, right is and
                                        let inner = vec![left,right,left2,right2];
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    } else { // left is and, right is not Mand or And
                                        let inner = vec![left,right,next_state];
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    }
                                } else {
                                    if let Expression::MAnd(mut inner) = *next_state{ // left is not Mand or And, right is Mand
                                        inner.insert(0,state);
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    } else if let Expression::And(left2,right2) = *next_state { // left is not Mand or And, right is and
                                        let inner = vec![state,left2,right2];
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    } else { // left is not Mand or And, right is not Mand or And
                                        stack.push(Box::new(Expression::And(state, next_state)));
                                    }
                                }
                                if breaking & !top_layer {
                                    break;
                                }
                            }
                            OR_SYM => {
                                let next_state = stack.pop().unwrap(); // right

                                // if left is MOR then we need to add to the MOR
                                if let Expression::MOr(mut inner) = *state{
                                    inner.append(&mut vec![next_state]);
                                    stack.push(Box::new(Expression::MOr(inner)));
                                } else if let Expression::Or(left,right) = state.as_ref(){
                                    let inner = vec![left.clone(),right.clone(),next_state];
                                    let state = Box::new(Expression::MOr(inner));
                                    stack.push(state);
                                } else {
                                    let state = Box::new(Expression::Or(state, next_state));
                                    stack.push(state);
                                }
                            }
                            IMPL_SYM => {
                                let mut next_state = stack.pop().unwrap(); // right
                                let state = Box::new(Expression::Neg(state));

                                if let Expression::MOr(mut inner) = *next_state{
                                    inner.push(state.clone());
                                    next_state = Box::new(Expression::MOr(inner));
                                } else if let Expression::Or(left,right) = next_state.as_ref(){
                                    let inner = vec![left.clone(),right.clone(),state.clone()];
                                    next_state = Box::new(Expression::MOr(inner));
                                } else {
                                    next_state = Box::new(Expression::Or(state.clone(), next_state));
                                }
                                stack.push(next_state);
                            }
                            IFF_SYM => {
                                let next_state = stack.pop().unwrap(); // right
                                let neg_state = Box::new(Expression::Neg(state.clone()));
                                let neg_next_state = Box::new(Expression::Neg(next_state.clone()));
                                let left_impl = Box::new(Expression::Or(neg_state, next_state.clone()));
                                let right_impl = Box::new(Expression::Or(neg_next_state, state.clone()));
                                let state = Box::new(Expression::And(left_impl, right_impl));
                                stack.push(state);
                            }
                            UNTIL => {
                                let next_state = stack.pop().unwrap(); // right
                                let state = Box::new(Expression::U(state, next_state));
                                stack.push(state);
                            }
                            RELEASE => {
                                let next_state = stack.pop().unwrap(); // right
                                let state = Box::new(Expression::R(state, next_state));
                                stack.push(state);
                            }
                            _ => {unreachable!("Should not have gotten here");}
                        }
                    }
                    "(" => { // Initial parenthesis case
                        recurse_down(captures, stack,output, pushed_break, false);
                    }
                    ")" => {
                        break;
                    }
                    _ => {
                        stack.push(Box::new(Expression::Literal(Literal::Atom(token.to_string()))));
                    }
                }
                if pushed_break {
                    break;
                }
            }});}

    // Recurse down the expression and get the result
    recurse_down(&mut captures, &mut stack, &mut output, false, true);
    let x = stack.pop().unwrap();
    return x;
}

/// This function will take the expression and return the CDF form of the expression
pub fn input_to_expression_optimized(expression: &str, _layers: &i32, symbol_map: &mut SymbolMap, max_gate_number: &mut i32) -> Box<Expression> {
    // Build the regex pattern dynamically
    // set time
    let pattern = r"~([^)(/]+)";
    let re = Regex::new(&pattern).unwrap();
    // Split the input on `->`
    let parts: Vec<&str> = expression.split("->").collect();

    // Perform the replacement on each part
    let replaced_parts: Vec<String> = parts.iter()
        .map(|part| re.replace_all(part, "(~$1)").to_string())
        .collect();
    // Join the parts back together with `->`
    let result = replaced_parts.join("->");

    // let binding = cow.to_string();
    // let mut results = binding.as_str();
    // Get out the regex
    let re = Regex::new(&format!(
        "({}|{}|{}|{}|{}|{}|{}|{}|{}|{}|{}|\\(|\\)|\\d+(?:-\\d+)*|[a-zA-Z'_0-9\\[\\]]+(?:-[a-zA-Z'_0-9\\[\\]]+)*|-)",
        regex::escape(AND_SYM),
        regex::escape(OR_SYM),
        TRUE_SYM,
        FALSE_SYM,
        NEG_SYM,
        IMPL_SYM,
        IFF_SYM,
        regex::escape(GLOBAL_CHECK),
        regex::escape(EVENTUALLY_CHECK),
        regex::escape(UNTIL_CHECK),
        regex::escape(RELEASE_CHECK)
    )).unwrap();
    let mut captures = re.captures_iter(result.as_str());
    let mut stack: Vec<Box<Expression>> = Vec::new();
    let mut output: Vec<Box<Expression>> = Vec::new();

    /// This function will recurse down and pull out the CDF from the expression
    /// It will then return the result of the recursion where each and is a transition to be added to the fsm
    fn recurse_down(captures: &mut CaptureMatches, stack: &mut Vec<Box<Expression>>, output: &mut Vec<Box<Expression>>, pushed_break : bool, _top_layer: bool, symbol_map: &mut SymbolMap, max_gate_number: &mut i32) {
        stacker::maybe_grow(32*1024,1024*1024, || {
            while let Some(cap) = captures.next() {
                let token = cap.get(1).unwrap().as_str();
                match token {
                    TRUE_SYM => {
                        stack.push(Box::new(Expression::True));
                    }
                    FALSE_SYM => {
                        stack.push(Box::new(Expression::False));
                    }
                    // Only one expression inside of it (i.e. unary operators)
                    NEG_SYM | GLOBAL | EVENTUALLY => {
                        let mut breaking = false;
                        let next_token = captures.next().unwrap().get(1).unwrap().as_str();
                        // do we recurse or not
                        if (next_token == "(") | (next_token == GLOBAL) | (next_token == EVENTUALLY) {
                            recurse_down(captures, stack, output, pushed_break, false, symbol_map, max_gate_number);
                            if next_token != "(" { // We break if we are recursing with anything other than (
                                breaking = true;
                            }
                        } else {
                            let formatted_literal = format_literal(&mut next_token.to_string(), symbol_map, max_gate_number);
                            stack.push(Box::new(Expression::Literal(Literal::Atom(formatted_literal.to_string()))));
                        }
                        // match the token
                        single_expression_token_match(stack, token);
                        // If we recursed then break
                        if breaking{
                            break;
                        }
                    }
                    // Two expressions inside of it (i.e. binary operators)
                    AND_SYM | OR_SYM | IMPL_SYM | IFF_SYM | UNTIL | RELEASE => {
                        let mut breaking = false;
                        let state = stack.pop().unwrap(); // left
                        let next_token = captures.next().unwrap().get(1).unwrap().as_str();
                        if next_token.contains("(") | (next_token == GLOBAL) | (next_token == EVENTUALLY) | (next_token == NEG_SYM){
                            if next_token == NEG_SYM {
                                recurse_down(captures, stack, output, true, false, symbol_map, max_gate_number);
                            } else{
                                recurse_down(captures, stack, output, pushed_break, false, symbol_map, max_gate_number);
                            }
                            // Deal with next states
                            single_expression_token_match(stack, next_token);
                            if next_token != "("  { // We break if we are recursing with anything other than (
                                breaking = true;
                            }
                        }
                        else {
                            let formatted_literal = format_literal(&mut next_token.to_string(), symbol_map, max_gate_number);
                            stack.push(Box::new(Expression::Literal(Literal::Atom(formatted_literal.to_string()))));
                        }
                        // if it was orignally matched with AND_SYM
                        match token {
                            AND_SYM => {
                                let next_state = stack.pop().unwrap(); // right

                                // Check if we can do a MAnd
                                if let Expression::MAnd(mut inner) = *state{ // left lets Mand
                                    if let Expression::MAnd(mut inner2) = *next_state{ // right lets Mand
                                        inner.append(&mut inner2);
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    } else if let Expression::And(left2,right2) = *next_state { // just left is Mand, but right is and
                                        inner.push(left2);
                                        inner.push(right2);
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    } else { // just left is Mand, right is not Mand or And
                                        inner.push(next_state);
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    }
                                } else if let Expression::And(left,right) = *state{
                                    if let Expression::MAnd(mut inner) = *next_state{ // left is and, right is Mand
                                        inner.push(left);
                                        inner.push(right);
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    } else if let Expression::And(left2,right2) = *next_state { // left is and, right is and
                                        let inner = vec![left,right,left2,right2];
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    } else { // left is and, right is not Mand or And
                                        let inner = vec![left,right,next_state];
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    }
                                } else {
                                    if let Expression::MAnd(mut inner) = *next_state{ // left is not Mand or And, right is Mand
                                        inner.insert(0,state);
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    } else if let Expression::And(left2,right2) = *next_state { // left is not Mand or And, right is and
                                        let inner = vec![state,left2,right2];
                                        stack.push(Box::new(Expression::MAnd(inner)));
                                    } else { // left is not Mand or And, right is not Mand or And
                                        stack.push(Box::new(Expression::And(state, next_state)));
                                    }
                                }
                                if breaking{
                                    break;
                                }
                            }
                            OR_SYM => {
                                let next_state = stack.pop().unwrap(); // right

                                // if left is MOR then we need to add to the MOR
                                if let Expression::MOr(mut inner) = *state{
                                    inner.append(&mut vec![next_state]);
                                    stack.push(Box::new(Expression::MOr(inner)));
                                } else if let Expression::Or(left,right) = state.as_ref(){
                                    let inner = vec![left.clone(),right.clone(),next_state];
                                    let state = Box::new(Expression::MOr(inner));
                                    stack.push(state);
                                } else {
                                    let state = Box::new(Expression::Or(state, next_state));
                                    stack.push(state);
                                }
                            }
                            IMPL_SYM => {
                                let mut next_state = stack.pop().unwrap(); // right
                                let state = Box::new(Expression::Neg(state));

                                if let Expression::MOr(mut inner) = *next_state{
                                    inner.push(state.clone());
                                    next_state = Box::new(Expression::MOr(inner));
                                } else if let Expression::Or(left,right) = next_state.as_ref(){
                                    let inner = vec![left.clone(),right.clone(),state.clone()];
                                    next_state = Box::new(Expression::MOr(inner));
                                } else {
                                    next_state = Box::new(Expression::Or(state.clone(), next_state));
                                }
                                stack.push(next_state);

                                // THH TRYING
                                // let mut next_state = stack.pop().unwrap(); // right
                                // let try_state = Box::new(Expression::Implies(state,next_state));
                                // stack.push(try_state);

                            }
                            IFF_SYM => {
                                let next_state = stack.pop().unwrap(); // right
                                let neg_state = Box::new(Expression::Neg(state.clone()));
                                let neg_next_state = Box::new(Expression::Neg(next_state.clone()));
                                let left_impl = Box::new(Expression::Or(neg_state, next_state.clone()));
                                let right_impl = Box::new(Expression::Or(neg_next_state, state.clone()));
                                let state = Box::new(Expression::And(left_impl, right_impl));
                                stack.push(state);
                            }
                            UNTIL => {
                                let next_state = stack.pop().unwrap(); // right
                                let state = Box::new(Expression::U(state, next_state));
                                stack.push(state);
                            }
                            RELEASE => {
                                let next_state = stack.pop().unwrap(); // right
                                let state = Box::new(Expression::R(state, next_state));
                                stack.push(state);
                            }
                            // _ => {unreachable!("Should not have gotten here");}
                            _ => {unreachable!("(!)HyperRust Error. Binary operators must be in the form of <L_expr><op><R_expr>.\n");}
                        }
                    }
                    "(" => { // Initial parenthesis case
                        recurse_down(captures, stack,output, pushed_break, false, symbol_map, max_gate_number);
                    }
                    ")" => {
                        break;
                    }
                    _ => {
                        let formatted_literal = format_literal(&mut token.to_string(), symbol_map, max_gate_number);
                        stack.push(Box::new(Expression::Literal(Literal::Atom(formatted_literal.to_string()))));
                    }
                }
            }});}

    // Recurse down the expression and get the result while we still have captures
    // check how many elements are left in captures)
    recurse_down(&mut captures, &mut stack, &mut output, false, true, symbol_map, max_gate_number);
    let x = stack.pop().unwrap();
    return x;
}

#[cfg(test)]
mod tests {
    use super::*;
    fn get_debug() -> bool{
        return false;
    }

    #[test]
    fn test_simple_input_to_expression() {
        // This test should return MAnd([Implies(Literal(Atom("a")), Literal(Atom("a")))])
        // Or that a always goes to itself
        let debug = get_debug();
        let expression = r"((a)  ->  (a'))";
        let fsm = input_to_expression(expression);
        if debug {
            // println!("{:?}", fsm);
        }
        let expr1 = Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom("a".to_string())))));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("a'".to_string())));
        let res = Box::new(Expression::Or(expr1,expr2));
        assert_eq!(fsm, res);
    }

    #[test]
    fn test_single_or(){
        // This test should return MAnd([MOr([Literal(Atom("a")),Literal(Atom("b"))])])
        // Or that a or b is the next state
        let debug = get_debug();
        let expression = r"((a)->(a'\/b'))"; // Which translates to not(a) \/ (a or b)
        let fsm = input_to_expression(expression);
        if debug {
            // println!("{:?}", fsm);
        }
        let expr1 = Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom("a".to_string())))));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("a'".to_string())));
        let expr3 = Box::new(Expression::Literal(Literal::Atom("b'".to_string())));
        let res = Box::new(Expression::MOr(vec![expr2,expr3,expr1]));
        assert_eq!(fsm, res);
    }

    #[test]
    fn test_no_parentheses(){
        let debug = get_debug();
        let expression = r"a->a'\/b'"; // Which translates to not(a) \/ (a or b) which is then MOR
        let fsm = input_to_expression(expression);
        if debug {
            // println!("{:?}", fsm);
        }
        let expr1 = Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom("a".to_string())))));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("a'".to_string())));
        let expr3 = Box::new(Expression::Literal(Literal::Atom("b'".to_string())));
        let res = Box::new(Expression::MOr(vec![expr1,expr2,expr3]));
        assert_eq!(fsm, res);
    }


    #[test]
    fn test_complex(){
        let expression = r"((a)->(a'\/~a'))/\(~a->(~a'))";
        let fsm = input_to_expression(expression);
        // println!("{:?}", fsm);
        let expr1 = Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom("a'".to_string())))));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("a'".to_string())));
        let expr3 = Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom("a".to_string())))));
        let res1 = Box::new(Expression::MOr(vec![expr2,expr1,expr3]));

        let expr5 = Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom("a".to_string())))));
        let expr6 = Box::new(Expression::Literal(Literal::Atom("a'".to_string())));
        let expr7 = Box::new(Expression::Neg(expr5)); // double negation on right of and
        let expr8 = Box::new(Expression::Neg(expr6)); // negation of a'
        let res2 = Box::new(Expression::Or(expr7,expr8)); // right of the and
        let res = Box::new(Expression::And(res1,res2));
        assert_eq!(fsm, res);

    }

    #[test]
    fn test_double_implication(){
        let expression = r"(a<->b)"; // Which translates to (a -> b) /\ (b -> a)
        let fsm = input_to_expression(expression);
        // println!("{:?}", fsm);
        let expr1 = Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom("a".to_string())))));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("b".to_string())));
        let res1 = Box::new(Expression::Or(expr1,expr2)); // a -> b

        let expr3 = Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom("b".to_string())))));
        let expr4 = Box::new(Expression::Literal(Literal::Atom("a".to_string())));
        let res2 = Box::new(Expression::Or(expr3,expr4)); // b -> a
        let res = Box::new(Expression::And(res1,res2));
        assert_eq!(fsm, res);
    }

    #[test]
    fn test_broken_edge(){
        let expression = r"(((b/\a)->((~a')/\b')))"; // this was previously broken
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        // println!("{:?}", fsm);
        let expr1 = Box::new(Expression::Literal(Literal::Atom("a".to_string())));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("b".to_string())));
        let res1 = Box::new(Expression::And(expr2,expr1)); // a /\ b

        let expr3 = Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom("a'".to_string())))));
        let expr4 = Box::new(Expression::Literal(Literal::Atom("b'".to_string())));
        let res2 = Box::new(Expression::And(expr3,expr4)); // ~a' /\ b'
        let res1 = Box::new(Expression::Neg(res1)); // ~(a /\ b)
        let res = Box::new(Expression::Or(res1,res2));
        assert_eq!(fsm, res);
    }

    #[test]
    fn test_global(){
        let expression = r"G(a)";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        assert_eq!(fsm, Box::new(Expression::G(Box::new(Expression::Literal(Literal::Atom("a".to_string()))))));
    }

    #[test]
    fn test_multiple_global(){
        let expression = r"G(a) /\ G(b)";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let expr1 = Box::new(Expression::G(Box::new(Expression::Literal(Literal::Atom("a".to_string())))));
        let expr2 = Box::new(Expression::G(Box::new(Expression::Literal(Literal::Atom("b".to_string())))));
        let res = Box::new(Expression::And(expr1,expr2));
        assert_eq!(fsm, res);

        let  expression = r"G(a \/ b)";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let expr1 = Box::new(Expression::Literal(Literal::Atom("a".to_string())));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("b".to_string())));
        let res = Box::new(Expression::G(Box::new(Expression::Or(expr1,expr2))));
        assert_eq!(fsm, res);

        let expression = r"G(b\/a)/\G(a/\b)";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let expr1 = Box::new(Expression::Literal(Literal::Atom("a".to_string())));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("b".to_string())));
        let res1 = Box::new(Expression::Or(expr2.clone(),expr1.clone()));
        let res1 = Box::new(Expression::G(res1));

        let res2 = Box::new(Expression::And(expr1.clone(),expr2.clone()));
        let res2 = Box::new(Expression::G(res2));
        let res = Box::new(Expression::And(res1,res2));
        assert_eq!(fsm, res);

        let expression = r"F(~(b\/a))/\G(a/\b)";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let expr1 = Box::new(Expression::Literal(Literal::Atom("a".to_string())));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("b".to_string())));
        let res1 = Box::new(Expression::Or(expr2.clone(),expr1.clone()));
        let res1 = Box::new(Expression::F(Box::new(Expression::Neg(res1))));

        let res2 = Box::new(Expression::And(expr1.clone(),expr2.clone()));
        let res2 = Box::new(Expression::G(res2));
        let res = Box::new(Expression::And(res1,res2));
        assert_eq!(fsm, res);

        let expression = r"~(G(a)/\G(b))";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let expr1 = Box::new(Expression::G(Box::new(Expression::Literal(Literal::Atom("a".to_string())))));
        let expr2 = Box::new(Expression::G(Box::new(Expression::Literal(Literal::Atom("b".to_string())))));
        let res = Box::new(Expression::And(expr1,expr2));
        let res = Box::new(Expression::Neg(res));
        assert_eq!(fsm, res);
    }

    #[test]
    fn test_until(){
        let expression = r"(a)U(b)";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let expr1 = Box::new(Expression::Literal(Literal::Atom("a".to_string())));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("b".to_string())));
        let res = Box::new(Expression::U(expr1,expr2));
        assert_eq!(fsm, res);

        let expression = r"(a)U((b)U(c))";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let expr1 = Box::new(Expression::Literal(Literal::Atom("a".to_string())));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("b".to_string())));
        let expr3 = Box::new(Expression::Literal(Literal::Atom("c".to_string())));
        let res1 = Box::new(Expression::U(expr2,expr3));
        let res = Box::new(Expression::U(expr1,res1));
        assert_eq!(fsm, res);

        let expression = r"((a)U(b))/\G(a)";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let expr1 = Box::new(Expression::Literal(Literal::Atom("a".to_string())));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("b".to_string())));
        let res1 = Box::new(Expression::U(expr1.clone(),expr2));
        let expr3 = Box::new(Expression::G(expr1.clone()));
        let res = Box::new(Expression::And(res1,expr3));
        assert_eq!(fsm, res);

    }

    #[test]
    fn test_prime(){
        let expression = r"((a'/\b')/\c)";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let expr1 = Box::new(Expression::Literal(Literal::Atom("a'".to_string())));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("b'".to_string())));
        let expr3 = Box::new(Expression::Literal(Literal::Atom("c".to_string())));
        let res = Box::new(Expression::MAnd(vec![expr1.clone(),expr2.clone(),expr3.clone()]));
        assert_eq!(fsm, res);

        let expression = r"((~a'/\~b')/\c)";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let na = Box::new(Expression::Neg(expr1.clone()));
        let nb = Box::new(Expression::Neg(expr2.clone()));
        let res = Box::new(Expression::MAnd(vec![na,nb,expr3.clone()]));
        assert_eq!(fsm, res);

        let expression = r"(~FAIL'/\(newnode_1'/\~newnode_0')/\~popRightFAIL')";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let fail = Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom("FAIL'".to_string())))));
        let newnode_1 = Box::new(Expression::Literal(Literal::Atom("newnode_1'".to_string())));
        let newnode_0 = Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom("newnode_0'".to_string())))));
        let popRightFAIL = Box::new(Expression::Neg(Box::new(Expression::Literal(Literal::Atom("popRightFAIL'".to_string())))));
        let res = Box::new(Expression::MAnd(vec![fail,newnode_1,newnode_0,popRightFAIL]));
        assert_eq!(fsm, res);

    }

    #[test]
    fn test_m_functions(){
        let expression = r"((a/\b)/\c)";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let expr1 = Box::new(Expression::Literal(Literal::Atom("a".to_string())));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("b".to_string())));
        let expr3 = Box::new(Expression::Literal(Literal::Atom("c".to_string())));
        let res = Box::new(Expression::MAnd(vec![expr1,expr2,expr3]));
        assert_eq!(fsm, res);

        let expression = r"(a\/b\/c)";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let expr1 = Box::new(Expression::Literal(Literal::Atom("a".to_string())));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("b".to_string())));
        let expr3 = Box::new(Expression::Literal(Literal::Atom("c".to_string())));
        let res = Box::new(Expression::MOr(vec![expr1,expr2,expr3]));
        assert_eq!(fsm, res);

        let expression = r"(a/\b/\c)/\(a\/b\/c)";
        // println!("{:?}", expression); // becomes a and b and c and (a or b or c)
        let fsm = input_to_expression(expression);
        let expr1 = Box::new(Expression::Literal(Literal::Atom("a".to_string())));
        let expr2 = Box::new(Expression::Literal(Literal::Atom("b".to_string())));
        let expr3 = Box::new(Expression::Literal(Literal::Atom("c".to_string())));
        let res1 = Box::new(Expression::MOr(vec![expr1.clone(),expr2.clone(),expr3.clone()]));
        let res = Box::new(Expression::MAnd(vec![expr1.clone(),expr2.clone(),expr3.clone(),res1]));
        assert_eq!(fsm, res);
    }

    #[test]
    fn test_broken_snark() {
        let expression = r"(~a/\~b/\c)";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        let a = Box::new(Expression::Literal(Literal::Atom("a".to_string())));
        let b = Box::new(Expression::Literal(Literal::Atom("b".to_string())));
        let c = Box::new(Expression::Literal(Literal::Atom("c".to_string())));
        let res1 = Box::new(Expression::MAnd(vec![Box::new(Expression::Neg(a.clone())),Box::new(Expression::Neg(b.clone())),c.clone()]));
        // println!("{:?}", fsm);
        assert_eq!(fsm, res1);


        let expression = r"~(G(~FAIL[A])";
        // println!("{:?}", expression);
        let fsm = input_to_expression(expression);
        // println!("{:?}", fsm);
        let fail = Box::new(Expression::Literal(Literal::Atom("FAIL[A]".to_string())));
        let res1 = Box::new(Expression::Neg(Box::new(Expression::G(Box::new(Expression::Neg(fail))))));
        assert_eq!(fsm, res1);


        // test a snark case
        let expression = r"~(G(~FAIL[A]) /\ F~(((proc1-popRightSTART[A] <-> proc1-popRightSTART[B]) /\ (proc1-popRightEND[A] <-> proc1-popRightEND[B]))))";
        let proc1_popRightSTART_A = Box::new(Expression::Literal(Literal::Atom("proc1-popRightSTART[A]".to_string())));
        let proc1_popRightSTART_B = Box::new(Expression::Literal(Literal::Atom("proc1-popRightSTART[B]".to_string())));
        let proc1_popRightEND_A = Box::new(Expression::Literal(Literal::Atom("proc1-popRightEND[A]".to_string())));
        let proc1_popRightEND_B = Box::new(Expression::Literal(Literal::Atom("proc1-popRightEND[B]".to_string())));
        let fail = Box::new(Expression::Literal(Literal::Atom("FAIL[A]".to_string())));
        let not_proc1_popRightSTART_A = Box::new(Expression::Neg(proc1_popRightSTART_A.clone()));
        let not_proc1_popRightSTART_B = Box::new(Expression::Neg(proc1_popRightSTART_B.clone()));
        let not_proc1_popRightEND_A = Box::new(Expression::Neg(proc1_popRightEND_A.clone()));
        let not_proc1_popRightEND_B = Box::new(Expression::Neg(proc1_popRightEND_B.clone()));
        let or1 = Box::new(Expression::Or(not_proc1_popRightSTART_A.clone(),proc1_popRightSTART_B.clone()));
        let or2 = Box::new(Expression::Or(not_proc1_popRightSTART_B.clone(),proc1_popRightSTART_A.clone()));
        let or3 = Box::new(Expression::Or(not_proc1_popRightEND_A.clone(),proc1_popRightEND_B.clone()));
        let or4 = Box::new(Expression::Or(not_proc1_popRightEND_B.clone(),proc1_popRightEND_A.clone()));
        let mand = Box::new(Expression::MAnd(vec![or1,or2,or3,or4]));
        let fmand = Box::new(Expression::Neg(mand));
        let ffail = Box::new(Expression::Neg(fail));
        let fin = Box::new(Expression::F(fmand.clone()));
        let gfail = Box::new(Expression::G(ffail));
        let res = Box::new(Expression::Neg(Box::new(Expression::And(gfail,fin))));
        let fsm = input_to_expression(expression);
        // println!("{:?}", fsm);
        assert_eq!(fsm, res);
    }
}