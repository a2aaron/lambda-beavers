#![feature(iter_intersperse)]
#![feature(hash_set_entry)]
mod debruijn;
mod graph;
mod parse_debruijn;
mod parse_term;
mod reduce;
mod replace;
mod term;

use crate::{debruijn::call, graph::ReductionGraph};

pub fn print(graph: &ReductionGraph) {
    println!("digraph G {{");

    for (i, node) in graph.nodes.iter().enumerate() {
        println!("{} [label = \"{}\"];", i, node);
    }
    for (a, b) in &graph.edges {
        println!("{} -> {}", a.0, b.0);
    }
    println!("}}");
}

pub fn reduce_full(graph: &mut ReductionGraph) {
    loop {
        if graph.nodes.len() > 100 || !graph.any_reducible() {
            break;
        }
        graph.reduce_node(graph.unreduced_nodes[0]);
    }
}

#[allow(unused_variables)]
fn main() {
    let ident_term = "λx.x";
    let true_term = "λx.λy.x";
    let false_term = "λx.λy.y";
    let and_term = "λp.λq.p q p";
    let succ_term = "λn.λf.λx.f (n f x)";
    let plus_term = "λm.λn.λf.λx.m f (n f x)";
    let mult_term = "λm.λn.λf.λx.m m ";
    let zero_term = "λf.λx.x";
    let one_term = "λf.λx.f x";
    let two_term = "λf.λx.f (f x)";
    let three_term = "λf.λx.f (f (f x))";
    let four_term = "λf.λx.f (f (f (f x)))";
    let five_term = "λf.λx.f (f (f (f (f x))))";

    // println!("IDENT = {}", ident_term);
    // println!("TRUE = {}", true_term);
    // println!("FALSE = {}", false_term);
    // println!("AND = {}", and_term);
    // println!("PLUS = {}", plus_term);
    // println!("ZERO = {}", zero_term);
    // println!("ONE = {}", one_term);
    // println!("TWO = {}", two_term);
    // println!("THREE = {}", three_term);
    // println!("FOUR = {}", four_term);
    // println!("FIVE = {}", five_term);
    // let combined = call(call(and_term, true_term), false_term);
    // println!("AND TRUE FALSE = {}", combined);
    // let combined = call(succ_term, zero_term);
    // println!("SUCC ZERO = {}", combined);
    // let combined = call(call(plus_term, three_term.clone()), five_term.clone());
    // println!("PLUS THREE FIVE = {}", combined);
    // println!("---");
    // let mult_term = "λm.λn.λf.m (n f)";
    let mult_term = "λn. λm. λf. λx. (λa. (λm. λn. λf. λx. m f (n f x)) n a f x) m f x";
    let combined = call(call(and_term, true_term), false_term);
    let mut graph = ReductionGraph::with_root(combined);
    reduce_full(&mut graph);
    print(&graph);
}
