use std::str::FromStr;

use clap::{Parser, ValueEnum, command};
use lambda_beaver::common_terms::{self};

use lambda_beaver::reduce::{ReductionStrategy, ReductionStrategyKind};
use lambda_beaver::replace::VisitOrder;
use lambda_beaver::term::Term;
use lambda_beaver::{debruijn::Debruijn, graph::ReductionGraph};

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum NodeLabelType {
    Debruijn,
    DebruijnCommonTerm,
    Binary,
    BinaryLen,
    Classic,
}

impl NodeLabelType {
    pub fn to_string(&self, term: &Debruijn) -> String {
        match self {
            NodeLabelType::Debruijn => format!("{}", term),
            NodeLabelType::DebruijnCommonTerm => common_terms::to_string(term),
            NodeLabelType::Binary => format!("{:b}", term),
            NodeLabelType::BinaryLen => format!("{:b}", term).len().to_string(),
            NodeLabelType::Classic => format!("{}", Term::from(term)),
        }
    }
}

pub fn to_graphviz(graph: &ReductionGraph, node_label: NodeLabelType) -> String {
    let mut output = vec![];
    output.push(format!("strict digraph G {{"));

    if let Some(root) = graph.root {
        let root = format!("{} [color = red];", root.0);
        output.push(root);
    }
    if let Some(brnf) = graph.beta_reduced_normal_form {
        let brnf = format!("{} [color = blue];", brnf.0);
        output.push(brnf);
    }
    for (i, node) in graph.nodes().iter().enumerate() {
        let label = node_label.to_string(&node.term);
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
                // TODO: select this via strategy
                let redex_index = graph.get(node_to_reduce).unwrap().unevaluated_redexes[0];
                let graph_update = graph.reduce_node(node_to_reduce, redex_index);
                if graph_update.is_brnf {
                    brnf_found_at = Some(i);
                }

                let brnf_message = if let Some(brnf_found_at) = brnf_found_at {
                    format!("found @ {}", brnf_found_at)
                } else {
                    format!("not found")
                };
                println!(
                    "{i}/{max} - {} unevaluated redexes remain (+{} this reduction) | BRNF: {}",
                    graph.incomplete_nodes().len(),
                    graph_update
                        .new_node
                        .map(|idx| graph.get(idx).unwrap())
                        .map(|node| node.unevaluated_redexes.len())
                        .unwrap_or(0),
                    brnf_message
                );
            }
            None => {
                assert!(graph.incomplete_nodes().is_empty());
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
        graph.incomplete_nodes().len()
    );
}

#[derive(Parser, Debug)]
#[command(about, long_about = None)]
struct Args {
    /// Term to parse. This can be a classic or Debruijn term
    term: String,
    /// Maximum number of reductions to perform
    #[arg(short, long, default_value = "100")]
    max_reductions: usize,
    /// Reduction strategy to use
    #[arg(short, long, default_value = "bfs")]
    strategy: ReductionStrategyKind,
    /// Node label type to use in the graphviz output
    #[arg(short, long, default_value = "debruijn")]
    node_label: NodeLabelType,
    /// Output file for the graphviz representation
    #[arg(short, long("out"), default_value = "out.dot")]
    output: String,
}

fn main() {
    let args = Args::parse();

    let term = args.term;
    let term = match Debruijn::from_str(&term) {
        Ok(term) => term,
        Err(err) => {
            println!("Couldn't parse {term}. Reason: {err}");
            std::process::exit(1);
        }
    };
    let max_reductions = args.max_reductions;
    let strategy = ReductionStrategy::from(args.strategy);
    let node_label = args.node_label;
    let visit_order = VisitOrder::LEFT_OUTERMOST;
    let mut graph = ReductionGraph::with_root(term, visit_order);

    reduce_with_stats(&mut graph, strategy, max_reductions);
    let graphviz = to_graphviz(&graph, node_label);
    std::fs::write(&args.output, graphviz).expect("Failed to write Graphviz output");
}
