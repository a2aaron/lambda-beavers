#![feature(iter_intersperse)]
#![feature(hash_set_entry)]
#![feature(macro_metavar_expr_concat)]

mod common_terms;
mod debruijn;
mod graph;
mod parse_debruijn;
mod parse_term;
mod reduce;
mod replace;
mod term;

use crate::{common_terms::*, debruijn::call, graph::ReductionGraph, term::Term};

pub fn print(graph: &ReductionGraph) {
    println!("digraph G {{");

    for (i, node) in graph.nodes.iter().enumerate() {
        println!("{} [label = \"{}\"];", i, common_terms::to_string(node));
    }
    for (a, b) in &graph.edges {
        println!("{} -> {}", a.0, b.0);
    }
    println!("}}");
}

pub fn reduce_full(graph: &mut ReductionGraph) {
    loop {
        if graph.nodes.len() > 10000 || !graph.any_reducible() {
            break;
        }
        graph.reduce_node(graph.unreduced_nodes[0]);
    }
}

#[allow(unused_variables)]
fn main() {
    let combined = call(PLUS(), PLUS());
    let mut graph = ReductionGraph::with_root(combined);
    reduce_full(&mut graph);
    print(&graph);
}
