//! # mgcalc
//! 
//! `mgcalc` is a test project which provides a calculator in the terminal.
//! I usually have a terminal of some sort open, which typically does not support command line maths.
//! Yes it would be trivial to either install an existing program or just launch Python, but this way I also get to learn something new.
//! 
//! ## Examples
//! 
//! See the tests for a full overview of the functionality, but as I go I'll periodically update these examples.
//! Note that to use brackets, you may have to wrap the expression in quotation marks as Bash treats brackets in a special way.
//! 
//! - Mathematical operations
//! ```custom
//! $ mgcalc 2+3
//! 5
//! $ mgcalc 5-1/2
//! 4.5
//! $ mgcalc 2*2^7
//! 256
//! $ mgcalc "(-1)^3"
//! -1
//! ```
//! 
//! - Mathematical constants
//! ```custom
//! $ mgcalc 2*pi
//! 6.283185307179586
//! $ mgcalc "e^(-1)"
//! 0.36787944117144233
//! ```
//! 
//! - Complex numbers
//! ```custom
//! $ mgcalc 2i*pi
//! 0+6.283185307179586i
//! $ mgcalc "(13+14i)*(2.5+6j)"
//! -51.5+113i
//! $ mgcalc "(-1)^(0.25)""
//! 0.7071067811865476+0.7071067811865475i
//! ```

use std::f64::consts::{E, PI};
use std::error::Error;
use num::complex::Complex;


/// Generic stack class. Could likely implement as a `Vec<T>` directly.
/// Get a one with `Stack::new()`.
pub struct Stack<T> {
    stack: Vec<T>,
    top: usize,
}

/// Estimated upper bound to number of operations - for eps checking later.
const MAX_OPS: i32 = 40;

impl <T> Stack<T> {
    /// Create a new instance of `Stack<T>`.
    pub fn new() -> Self {
        Stack {
            stack: Vec::new(),
            top: 0,
    }}

    /// Add a new item to the top of the stack.
    pub fn push(&mut self, val: T) {
        self.top += 1;
        self.stack.push(val);
    }

    /// Remove an item from the top of the stack, or return `None` if the stack is empty.
    pub fn pop(&mut self) -> Option<T> {
        let val = self.stack.pop()?;
        self.top -= 1;
        Some(val)
    }

    /// Obtain the size of the stack.
    pub fn gettop(&self) -> usize {
        self.top
    }
}


/// Expression class. Initialise a new one directly with a `&str` using `Expression::new(s: &str)`, or using environment arguments using `Expression::from_args(args: Iterator<Item=String>)`.
pub struct Expression {
    expression: String,
    valuestack: Stack<String>,
    operatorstack: Stack<char>,
}

impl Expression {
    /// Create a new instance of Expression directly from a `&str`.
    pub fn new(expression: &str) -> Result<Self, &'static str> {
        Ok(Self { 
            expression: String::from(expression),
            valuestack: Stack::new(),
            operatorstack: Stack::new(),
    })}

    /// Create a new instance of Expression using `std::env::args()` directly.
    pub fn from_args(
        mut args: impl Iterator<Item = String>,
    ) -> Result<Self, &'static str> {
        args.next();

        let expression = match args.next() {
            Some(expr) => expr,
            None => return Err("Did not get an expression.")
        };

        Self::new(&expression.trim())
    }

    /// Obtain the string representation of the expression.
    pub fn get_expression(&self) -> &str {
        &self.expression
    }

    /// Work through the expression character by character, to add values and operators to the relevant stacks.
    fn parse(&mut self) -> Result<(), Box<dyn Error>> {
        // Loop through characters in the expression. Use `loop` rather than `for` or `while` so that we can evaluate sub-expressions inside brackets.
        let expression = self.expression.clone();
        let mut expr_iter = expression.chars();
        loop {
            let character_opt = expr_iter.next();
            match character_opt {

                // We have reached the end of the input expression. If no error experienced, we can break control flow.
                None => break,

                // Brackets denote a sub-expression.
                Some('(') => {

                    // Extract the new expression up to `)`.
                    let mut new_expr = String::from("");
                    loop {
                        let character_opt = expr_iter.next();
                        match character_opt {

                            // End of input reached before closing bracket found.
                            None => return Err("Syntax error: Missing `)`".into()),

                            // Closing bracket found - evaluate sub-expression.
                            Some(')') => break,

                            // Keep on extracting.
                            Some(character) => {
                                new_expr += &character.to_string();
                            },
                    }}

                    // Make the new expression.
                    let new_expression = Expression::new(new_expr.as_str())?;

                    // The last value should be an empty string unless there is nothing to pop.
                    let lastval = self.valuestack.pop().unwrap_or_else(|| {String::from("")});

                    // Put it back with the solution to the sub-expression.
                    self.valuestack.push(lastval + new_expression.solve()?.as_str());
                },

                // Pipe brackets denote absolute value. Evaluate in the same way as above

                // Continue with the expression.
                Some(character) => {

                    // Character is a digit, or a leading negative sign.
                    if (character.is_alphanumeric() | (character == '.')) | (
                        (character == '-') & (self.valuestack.gettop() == 0)
                    ) {
                        // Add it to the lastval string.
                        let lastval = self.valuestack.pop().unwrap_or_else(|| {String::from("")});
                        self.valuestack.push(lastval + &character.to_string());
                    
                    // Character is an operator.
                    } else if (self.valuestack.gettop() != 0) & (
                        (character == '+') |
                        (character == '-') | 
                        (character == '*') | 
                        (character == '/') |
                        (character == '^')
                    ) {
                        // If this is the first character, keep going. If not, check if we can simplify or not based on order-of-operations.
                        if self.operatorstack.gettop() > 0 {
                            let lastop = self.operatorstack.pop().unwrap();
                            let can_simplify = is_ok_to_simplify(char::from(lastop), character);

                            // Put the last operator back!
                            self.operatorstack.push(lastop);

                            if can_simplify {
                                self.simplify_expression_to_head()?;
                        }}

                        // All done. Add the operator to the stack.
                        self.operatorstack.push(character);

                        // Get ready to add new values - expect an empty string.
                        self.valuestack.push(String::from(""));

                    // Any other character not supported.
                    } else {
                        return Err("Unknown operator.".into());
                }},
        }}

        Ok(())
    }

    /// Combine the top two values on `valuestack` using the top operator on `operatorstack`.
    fn simplify_expression_to_head(&mut self) -> Result<(), Box<dyn Error>> {
        // Parse left- and right-hand-side of operation into floats.
        let rhs: Complex<f64> = parse_value(self.valuestack.pop().unwrap())?;
        let lhs: Complex<f64> = parse_value(self.valuestack.pop().unwrap())?;
        // Extract the operator.
        let lastop = self.operatorstack.pop().unwrap();

        // Calculate the value and push it to the stack.
        match lastop {
            '+' => self.valuestack.push((lhs + rhs).to_string()),
            '-' => self.valuestack.push((lhs - rhs).to_string()),
            '*' => self.valuestack.push((lhs * rhs).to_string()),
            '/' => self.valuestack.push((lhs / rhs).to_string()), 
            '^' => self.valuestack.push((lhs.powc(rhs)).to_string()),
             _   => return Err("Unknown operator.".into()),
        }
        
        Ok(())
    }

    /// Solve the expression. Parses the result onto the stacks containing values and operators, and then calculates the result.
    pub fn solve(mut self) -> Result<String, Box<dyn Error>> {
        // Parse the function into solvable form.
        self.parse()?;

        // Remove items from the stack in turn and evaluate.
        while self.valuestack.gettop() > 1 {
            self.simplify_expression_to_head()?;
        }

        // Any operators remaining at the end means that the user has used invalid syntax.
        if self.operatorstack.gettop() != 0 {
            Err("Syntax error - operators remaining.".into())
        } else {
            let value = self.valuestack.pop().unwrap().parse::<Complex<f64>>()?;
            match value {
                Complex{re: x, im: y} if (y.abs() < f64::EPSILON * MAX_OPS as f64) => Ok(x.to_string()),
                Complex{re: _, im: _} => Ok(value.to_string()),
            }
    }}
}


/// Test two operations to work out if the previous one can be evaluated following the order of operations:
/// 1) Brackets
/// 2) Exponentials
/// 3) Multiplication and Division
/// 4) Addition and Subtraction
pub fn is_ok_to_simplify(previous_op: char, following_op: char) -> bool {
    match (previous_op, following_op) {
        ('^', op) if (op == '+') | (op == '-') | (op == '*') | (op == '/') => {
            true
        },
        (mul, add) if ((mul == '*') | (mul == '/')) & ((add == '+') | (add == '-')) => {
            true
        },
        (_, _) => {
            false
        },
    }
}

/// Convert strings to floats.
/// Use a separate function rather than calling the `.parse()` method directly so that we can deal with constants such as `pi` and `e`.
pub fn parse_value(s: String) -> Result<Complex<f64>, Box<dyn Error>> {
    match s.to_lowercase().as_str() {
        "pi" => Ok(Complex::new(PI, 0.0)),
        "e"  => Ok(Complex::new(E, 0.0)),
        x if x.parse::<f64>().is_ok() => Ok(Complex::new(x.parse::<f64>()?, 0.0)),
        x if x.parse::<Complex<f64>>().is_ok() => Ok(x.parse::<Complex<f64>>()?),
        _ => Err("Value Error: Unknown value {s}".into()),
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_operations() -> Result<(), Box<dyn Error>> {
        let expression1 = Expression::new("1+1")?;
        let expression2 = Expression::new("4-2")?;
        let expression3 = Expression::new("2*1")?;
        let expression4 = Expression::new("4/2")?;
        assert!(
            ("2".parse::<Complex<f64>>()? - expression1.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        assert!(
            ("2".parse::<Complex<f64>>()? - expression2.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        assert!(
            ("2".parse::<Complex<f64>>()? - expression3.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        assert!(
            ("2".parse::<Complex<f64>>()? - expression4.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        Ok(())
    }

    #[test]
    fn no_operations() -> Result<(), Box<dyn Error>> {
        let expression = Expression::new("8")?;
        assert!(
            ("8".parse::<Complex<f64>>()? - expression.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        Ok(())
    }

    #[test]
    fn order_of_operations() -> Result<(), Box<dyn Error>> {
        let expression1 = Expression::new("1+2*3")?;
        let expression2 = Expression::new("1*3-2")?;
        assert!(
            ("7".parse::<Complex<f64>>()? - expression1.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        assert!(
            ("1".parse::<Complex<f64>>()? - expression2.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        Ok(())
    }

    #[test]
    fn double_digits() -> Result<(), Box<dyn Error>> {
        let expression1 = Expression::new("6*4-4")?;
        let expression2 = Expression::new("10+1")?;
        let expression3 = Expression::new("2+23")?;
        assert!(
            ("20".parse::<Complex<f64>>()? - expression1.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        assert!(
            ("11".parse::<Complex<f64>>()? - expression2.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        assert!(
            ("25".parse::<Complex<f64>>()? - expression3.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        Ok(())
    }

    #[test]
    fn negative_result() -> Result<(), Box<dyn Error>> {
        let expression = Expression::new("2-3")?;
        assert!(
            ("-1".parse::<Complex<f64>>()? - expression.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        Ok(())
    }

    #[test]
    fn floating_values() -> Result<(), Box<dyn Error>> {
        let expression1 = Expression::new("2.0*3.5")?;
        let expression2 = Expression::new("2.0*3.25")?;
        let expression3 = Expression::new("7/2")?;
        assert!(
            ("7".parse::<Complex<f64>>()? - expression1.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        assert!(
            ("6.5".parse::<Complex<f64>>()? - expression2.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        assert!(
            ("3.5".parse::<Complex<f64>>()? - expression3.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        Ok(())
    }

    #[test]
    fn leading_negative() -> Result<(), Box<dyn Error>> {
        let expression = Expression::new("-1+13")?;
        assert!(
            ("12".parse::<Complex<f64>>()? - expression.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        Ok(())
    }

    #[test]
    fn exponential() -> Result<(), Box<dyn Error>> {
        let expression1 = Expression::new("2^8+3")?;
        let expression2 = Expression::new("6*2+2^3")?;
        let expression3 = Expression::new("(-1)^3")?;
        assert!(
            (Complex::new(2.0, 0.0).powc(Complex::new(8.0, 0.0)) + 3.0 - expression1.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        assert!(
            (Complex::new(2.0, 0.0).powc(Complex::new(3.0, 0.0)) + 6.0*2.0 - expression2.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        assert!(
            (Complex::new(-1.0, 0.0).powc(Complex::new(3.0, 0.0)) - expression3.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
    
        Ok(())
    }

    #[test]
    fn brackets() -> Result<(), Box<dyn Error>> {
        let expression = Expression::new("6*(8+2)")?;
        assert!(
            ("60".parse::<Complex<f64>>()? - expression.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        Ok(())
    }

    #[test]
    fn operators_in_wrong_place() {
        let expression1 = Expression::new("*1").unwrap();
        let expression2 = Expression::new("1/").unwrap();
        let expression3 = Expression::new("1+-41").unwrap();
        assert!(expression1.solve().is_err());
        assert!(expression2.solve().is_err());
        assert!(expression3.solve().is_err());
    }

    #[test]
    fn constants() -> Result<(), Box<dyn Error>> {
        let expression1 = Expression::new("2*pi")?;
        let expression2 = Expression::new("2*e^(-3)")?;
        assert!(
            (Complex::new(2.0*PI, 0.0) - expression1.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        assert!(
            (Complex::new(2.0*E.powf(-3.0), 0.0) - expression2.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        Ok(())
    }

    #[test]
    fn complex_vals() -> Result<(), Box<dyn Error>> {
        let expression1 = Expression::new("2i")?;
        let expression2 = Expression::new("1+2i")?;
        let value = expression1.solve();
        /* 
        assert!(
            (Complex::new(0.0, 2.0) - expression1.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );
        assert!(
            (Complex::new(1.0, 2.0) - expression2.solve()?.parse::<Complex<f64>>()?).norm() < f64::EPSILON * MAX_OPS as f64
        );*/
        Ok(())
    }
}