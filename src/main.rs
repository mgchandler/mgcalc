use std::env;
use std::process;

use mgcalc::Expression;

fn main() {
    let expression = Expression::from_args(env::args()).unwrap_or_else(|err| {
        eprintln!("Problem parsing arguments: {err}");
        process::exit(1);
    });

    match expression.solve() {
        Ok(num) => println!("{num}"),
        Err(e)  => {
            eprintln!("Application error: {e}");
            process::exit(1);
        }
    };
}