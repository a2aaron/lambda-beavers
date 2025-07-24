#![feature(iter_intersperse)]

mod parse;
mod term;

use parse::{parse_program, pretty, tokenize};

use crate::term::{call, def, lit};

fn foo(program: &str) {
    println!("RAW   : {}", program);
    let tokens = tokenize(program);
    println!("TOKENS: {}", pretty(&tokens));
    match parse_program(&tokens) {
        Ok(program) => println!("PARSED: {}", program),
        Err(err) => println!("ERROR : {:?}", err),
    }
    println!("--------")
}

fn main() {
    let lambda = call(def("x", lit("x")), lit("y"));
    println!("{}", lambda);
    let lambda = def("x", call(lit("x"), lit("y")));
    println!("{}", lambda);
    println!("----");
    foo("(λx.x y)");

    foo("λx.x y");
    foo("λx.λy.x");
    foo("λx.λy.(x y)");
}
