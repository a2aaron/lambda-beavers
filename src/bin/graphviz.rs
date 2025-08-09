use std::str::FromStr;

use lambda_beaver::common_terms::{self};

use lambda_beaver::reduce::ReductionStrategy;
use lambda_beaver::{debruijn::Debruijn, graph::ReductionGraph};

pub enum NodeLabelType {
    Debruijn,
    DebruijnCommonTerm,
    Binary,
    BinaryLen,
}

impl NodeLabelType {
    pub fn to_string(&self, term: &Debruijn) -> String {
        match self {
            NodeLabelType::Debruijn => format!("{}", term),
            NodeLabelType::DebruijnCommonTerm => common_terms::to_string(term),
            NodeLabelType::Binary => format!("{:b}", term),
            NodeLabelType::BinaryLen => format!("{:b}", term).len().to_string(),
        }
    }
}

pub fn to_graphviz(graph: &ReductionGraph, node_label: NodeLabelType) -> String {
    let mut output = vec![];
    output.push(format!("digraph G {{"));

    if let Some(root) = graph.root {
        let root = format!("{} [color = red];", root.0);
        output.push(root);
    }
    if let Some(brnf) = graph.beta_reduced_normal_form {
        let brnf = format!("{} [color = blue];", brnf.0);
        output.push(brnf);
    }
    for (i, node) in graph.nodes().iter().enumerate() {
        let label = node_label.to_string(node);
        let node = format!("{} [label = \"{}\"];", i, label);
        output.push(node);
    }
    for (a, b) in graph.edges() {
        let edge = format!("{} -> {}", a.0, b.0);
        output.push(edge);
    }
    output.push(format!("}}"));
    output.join("\n")
}

pub fn reduce_with_stats(
    graph: &mut ReductionGraph,
    mut reduction_strategy: ReductionStrategy,
    max: usize,
) {
    let mut brnf_found_at = None;
    for i in 0..max {
        let node_to_reduce = reduction_strategy.get_node(graph);
        match node_to_reduce {
            Some(node_to_reduce) => {
                let graph_update = graph.reduce_node(node_to_reduce);
                if graph_update.is_brnf {
                    brnf_found_at = Some(i);
                }

                let brnf_message = if let Some(brnf_found_at) = brnf_found_at {
                    format!("found @ {}", brnf_found_at)
                } else {
                    format!("not found")
                };
                println!(
                    "{i}/{max} - {} unreduced nodes remain (+{} this reduction) | BRNF: {}",
                    graph.unreduced_nodes().len(),
                    graph_update.new_nodes.len(),
                    brnf_message
                );
            }
            None => {
                assert!(graph.unreduced_nodes().is_empty());
                println!("SUCCESS, no unreduced nodes remain");
                println!(
                    "{} total nodes, {} total edges",
                    graph.nodes().len(),
                    graph.edges().len()
                );
                return;
            }
        }
    }
    println!(
        "TIMEOUT REACHED - {} unreduced nodes remain",
        graph.unreduced_nodes().len()
    );
}

fn main() {
    // let term = call(call(MULT(), CHURCH(5)), CHURCH(3));
    let term = match std::env::args().nth(1) {
        Some(term) => term,
        None => {
            println!("expected an argument");
            std::process::exit(1);
        }
    };
    let term = match Debruijn::from_str(&term) {
        Ok(term) => term,
        Err(err) => {
            println!("Couldn't parse {term}. Reason: {err}");
            std::process::exit(1);
        }
    };
    let mut graph = ReductionGraph::with_root(term);
    reduce_with_stats(&mut graph, ReductionStrategy::BFS, 250);
    std::fs::write("out.dot", to_graphviz(&graph, NodeLabelType::Debruijn)).unwrap();
}
