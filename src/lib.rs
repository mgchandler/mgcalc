use std::f64::consts::{E, PI};
use std::error::Error;


pub struct Stack<T> {
    stack: Vec<T>,
    top: usize,
}

impl <T> Stack<T> {
    pub fn new() -> Self {
        Stack {
            stack: Vec::new(),
            top: 0,
    }}

    pub fn push(&mut self, val: T) {
        self.top += 1;
        self.stack.push(val);
    }

    pub fn pop(&mut self) -> Option<T> {
        let val = self.stack.pop();
        match val {
            Some(x) => {
                self.top -= 1;
                Some(x)
            },
            None => None
    }}

    pub fn gettop(&self) -> usize {
        self.top
    }
}


pub struct Expression {
    expression: String,
    valuestack: Stack<String>,
    operatorstack: Stack<char>,
}

impl Expression {
    pub fn new(expression: &str) -> Result<Self, &'static str> {
        Ok(Self { 
            expression: String::from(expression),
            valuestack: Stack::new(),
            operatorstack: Stack::new(),
    })}

    pub fn from_args(
        mut args: impl Iterator<Item = String>,
    ) -> Result<Self, &'static str> {
        args.next();

        let expression = match args.next() {
            Some(expr) => expr,
            None => return Err("Did not get an expression.")
        };

        Self::new(&expression)
    }

    pub fn get_expression(&self) -> &str {
        &self.expression
    }

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

    fn simplify_expression_to_head(&mut self) -> Result<(), Box<dyn Error>> {
        // Parse left- and right-hand-side of operation into floats.
        let rhs: f64 = parse_value(self.valuestack.pop().unwrap())?;
        let lhs: f64 = parse_value(self.valuestack.pop().unwrap())?;
        // Extract the operator.
        let lastop = self.operatorstack.pop().unwrap();

        // Calculate the value and push it to the stack.
        match lastop {
            '+' => self.valuestack.push((lhs + rhs).to_string()),
            '-' => self.valuestack.push((lhs - rhs).to_string()),
            '*' => self.valuestack.push((lhs * rhs).to_string()),
            '/' => self.valuestack.push((lhs / rhs).to_string()), 
            '^' => self.valuestack.push((lhs.powf(rhs)).to_string()),
             _   => return Err("Unknown operator.".into()),
        }
        
        Ok(())
    }

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
            Ok(self.valuestack.pop().unwrap())
    }}
}


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

pub fn parse_value(s: String) -> Result<f64, Box<dyn Error>> {
    match s.to_lowercase().as_str() {
        "pi" => Ok(PI),
        "e"  => Ok(E),
        x if x.parse::<f64>().is_ok() => Ok(x.parse::<f64>()?),
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
        assert_eq!("2", expression1.solve()?);
        assert_eq!("2", expression2.solve()?);
        assert_eq!("2", expression3.solve()?);
        assert_eq!("2", expression4.solve()?);
        Ok(())
    }

    #[test]
    fn no_operations() -> Result<(), Box<dyn Error>> {
        let expression = Expression::new("8")?;
        assert_eq!("8", expression.solve()?);
        Ok(())
    }

    #[test]
    fn order_of_operations() -> Result<(), Box<dyn Error>> {
        let expression1 = Expression::new("1+2*3")?;
        let expression2 = Expression::new("1*3-2")?;
        assert_eq!("7", expression1.solve()?);
        assert_eq!("1", expression2.solve()?);
        Ok(())
    }

    #[test]
    fn double_digits() -> Result<(), Box<dyn Error>> {
        let expression1 = Expression::new("6*4-4")?;
        let expression2 = Expression::new("10+1")?;
        let expression3 = Expression::new("2+23")?;
        assert_eq!("20", expression1.solve()?);
        assert_eq!("11", expression2.solve()?);
        assert_eq!("25", expression3.solve()?);
        Ok(())
    }

    #[test]
    fn negative_result() -> Result<(), Box<dyn Error>> {
        let expression = Expression::new("2-3")?;
        assert_eq!("-1", expression.solve()?);
        Ok(())
    }

    #[test]
    fn floating_values() -> Result<(), Box<dyn Error>> {
        let expression1 = Expression::new("2.0*3.5")?;
        let expression2 = Expression::new("2.0*3.25")?;
        let expression3 = Expression::new("7/2")?;
        assert_eq!("7",   expression1.solve()?);
        assert_eq!("6.5", expression2.solve()?);
        assert_eq!("3.5",   expression3.solve()?);
        Ok(())
    }

    #[test]
    fn leading_negative() -> Result<(), Box<dyn Error>> {
        let expression = Expression::new("-1+13")?;
        assert_eq!("12", expression.solve()?);
        Ok(())
    }

    #[test]
    fn exponential() -> Result<(), Box<dyn Error>> {
        let expression1 = Expression::new("2^8+3")?;
        let expression2 = Expression::new("6*2+2^3")?;
        let expression3 = Expression::new("(-1)^3")?;
        assert_eq!("259", expression1.solve()?);
        assert_eq!("20", expression2.solve()?);
        assert_eq!("-1", expression3.solve()?);
        Ok(())
    }

    #[test]
    fn brackets() -> Result<(), Box<dyn Error>> {
        let expression = Expression::new("6*(8+2)")?;
        assert_eq!("60", expression.solve()?);
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
        assert_eq!((2.0*PI).to_string(), expression1.solve()?);
        assert_eq!((2.0*E.powf(-3.0)).to_string(), expression2.solve()?);
        Ok(())
    }
}