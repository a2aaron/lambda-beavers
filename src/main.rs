#![feature(iter_intersperse)]
#![feature(hash_set_entry)]
mod debruijn;
mod graph;
mod parse;
mod reduce;
mod term;

use std::str::FromStr;

use crate::{
    debruijn::{call, Debruijn},
    graph::ReductionGraph,
    term::Term,
};
fn main() {
    let ident_term = compile("λx.x");
    let true_term = compile("λx.λy.x");
    let false_term = compile("λx.λy.y");
    let and_term = compile("λp.λq.p q p");
    let succ_term = compile("λn.λf.λx.f (n f x)");
    let plus_term = compile("λm.λn.λf.λx.m f (n f x)");
    let zero_term = compile("λf.λx.x");
    let one_term = compile("λf.λx.f x");
    let two_term = compile("λf.λx.f (f x)");
    let three_term = compile("λf.λx.f (f (f x))");
    let four_term = compile("λf.λx.f (f (f (f x)))");
    let five_term = compile("λf.λx.f (f (f (f (f x))))");

    println!("IDENT = {}", ident_term);
    println!("TRUE = {}", true_term);
    println!("FALSE = {}", false_term);
    println!("AND = {}", and_term);
    println!("PLUS = {}", plus_term);
    println!("ZERO = {}", zero_term);
    println!("ONE = {}", one_term);
    println!("TWO = {}", two_term);
    println!("THREE = {}", three_term);
    println!("FOUR = {}", four_term);
    println!("FIVE = {}", five_term);
    let combined = call(call(and_term, true_term), false_term);
    println!("AND TRUE FALSE = {}", combined);
    let combined = call(succ_term, zero_term);
    println!("SUCC ZERO = {}", combined);
    let combined = call(call(plus_term, three_term.clone()), five_term.clone());
    println!("PLUS THREE FIVE = {}", combined);
    println!("---");

    let mut graph = ReductionGraph::new(combined);
    graph::reduce_full(&mut graph);
    graph::print_nodes(&graph);
}

fn compile(arg: &str) -> Debruijn {
    let term = Term::from_str(arg).unwrap();
    let debruijn = Debruijn::try_from(term).unwrap();
    debruijn
}
