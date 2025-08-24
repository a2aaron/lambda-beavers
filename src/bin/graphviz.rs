use std::str::FromStr;

use clap::Parser;
use lambda_beaver::print::NodeLabelType;

use lambda_beaver::parse;
use lambda_beaver::reduce::{ReductionStrategy, ReductionStrategyKind};
use lambda_beaver::replace::VisitOrder;
use lambda_beaver::{debruijn::Debruijn, graph::ReductionGraph};

pub fn to_graphviz(graph: &ReductionGraph, node_label: NodeLabelType) -> String {
    let mut output = vec![];
    output.push(format!("strict digraph G {{"));

    if let Some((_, root)) = graph.root() {
        let root = format!("{} [color = red];", root);
        output.push(root);
    }
    if let Some((_, bnf)) = graph.bnf() {
        let bnf = format!("{} [color = blue];", bnf);
        output.push(bnf);
    }
    for (node, i) in graph.nodes() {
        let label = node_label.to_string(&node.term);
        let node = format!("{} [label = \"{}\"];", i, label);
        output.push(node);
    }
    for (a, b) in graph.edges() {
        let edge = format!("{} -> {}", a, b);
        output.push(edge);
    }
    output.push(format!("}}"));
    output.join("\n")
}

pub fn reduce_with_stats(
    graph: &mut ReductionGraph,
    mut reduction_strategy: ReductionStrategy,
    max: usize,
    stop_on_bnf: bool,
) {
    let mut bnf_found_at = None;
    for i in 0..max {
        let node_to_reduce = reduction_strategy.get_node(graph);
        match node_to_reduce {
            Some(node_to_reduce) => {
                // TODO: select this via strategy
                let redex_index = graph.get(node_to_reduce).unwrap().unevaluated_redexes[0];
                let graph_update = graph.reduce_node(node_to_reduce, redex_index);
                if graph_update.is_bnf {
                    bnf_found_at = Some(i);
                }

                let bnf_message = if let Some(bnf_found_at) = bnf_found_at {
                    format!("found @ {}", bnf_found_at)
                } else {
                    format!("not found")
                };
                println!(
                    "{i}/{max} - {} unevaluated redexes remain (+{} this reduction) | BNF: {}",
                    graph.incomplete_nodes().len(),
                    graph_update
                        .new_node
                        .map(|idx| graph.get(idx).unwrap())
                        .map(|node| node.unevaluated_redexes.len())
                        .unwrap_or(0),
                    bnf_message
                );
            }
            None => {
                assert!(graph.incomplete_nodes().is_empty());
                println!("SUCCESS, no unreduced nodes remain");
                println!(
                    "{} total nodes, {} total edges",
                    graph.nodes().count(),
                    graph.edges().len()
                );
                return;
            }
        }

        if stop_on_bnf && bnf_found_at.is_some() {
            println!("STOPING EARLY - BNF was found");
            return;
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
    #[arg(short, long, action)]
    stop_on_bnf: bool,
}

fn main() {
    let args = Args::parse();

    let term = args.term;
    let term = match Debruijn::from_str(&term) {
        Ok(term) => term,
        Err(err) => match parse::binary::from_str(&term) {
            Ok(term) => term,
            Err(binary_err) => {
                println!("Couldn't parse {term}. Reason: {err}, {:?}", binary_err);
                std::process::exit(1);
            }
        },
    };
    let max_reductions = args.max_reductions;
    let strategy = ReductionStrategy::from(args.strategy);
    let node_label = args.node_label;
    let visit_order = VisitOrder::LEFT_OUTERMOST;
    let stop_on_bnf = args.stop_on_bnf;
    let mut graph = ReductionGraph::with_root(term, visit_order);

    reduce_with_stats(&mut graph, strategy, max_reductions, stop_on_bnf);
    let graphviz = to_graphviz(&graph, node_label);
    std::fs::write(&args.output, graphviz).expect("Failed to write Graphviz output");
}
