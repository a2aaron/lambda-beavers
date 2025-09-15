use std::{ops::ControlFlow, str::FromStr};

use clap::Parser;
use lambda_beaver::{
    debruijn::Debruijn,
    debruijn_flat::{DebruijnNode, FlatRoot},
    parse,
    reduce::Reducer,
    treewalk::VisitOrder,
};

fn get_garbage_array(root: &FlatRoot) -> Vec<bool> {
    let mut is_garbage = vec![true; root.backing.len()];
    VisitOrder::LEFT_OUTERMOST.preorder_walk_2(root, |_, term, _| {
        is_garbage[term.term.0] = false;
        ControlFlow::Continue::<()>(())
    });

    is_garbage
}

fn to_node_label(term: DebruijnNode) -> String {
    match term {
        DebruijnNode::Index(index) => format!("idx_{index}"),
        DebruijnNode::Abstraction { usage, .. } => format!("abs, usage = {usage}"),
        DebruijnNode::Application { .. } => format!("app"),
    }
}

pub fn to_graph(root: &FlatRoot) -> String {
    let is_garbage = get_garbage_array(root);

    let mut output = vec![];
    output.push(format!("strict digraph G {{"));

    for (index, node) in root.backing.iter().enumerate() {
        let is_garbage = is_garbage[index];
        let node_color = if is_garbage {
            "grey"
        } else if index == root.root.0 {
            "red"
        } else {
            "black"
        };
        let label = format!("{} @ {index}", to_node_label(*node));
        let attribs = if is_garbage {
            format!("label=\"{label}\" color={node_color} fontcolor={node_color} constraint=false")
        } else {
            format!("label=\"{label}\" color={node_color} fontcolor={node_color}")
        };
        let node_text = format!("{index} [{attribs}]");
        output.push(node_text);

        let edge_color = if is_garbage { "grey" } else { "black" };
        match node {
            DebruijnNode::Index(_) => (),
            DebruijnNode::Abstraction { body, .. } => {
                output.push(format!("{index} -> {body} [color={edge_color}]"))
            }
            DebruijnNode::Application { func, arg } => {
                output.push(format!("{index} -> {func} [color={edge_color}]"));
                output.push(format!("{index} -> {arg} [color={edge_color}]"));
            }
        }
    }
    output.push(format!("}}"));
    output.join("\n")
}

#[derive(Parser, Debug)]
#[command(about, long_about = None)]
struct Args {
    /// Term to parse. This can be a classic or Debruijn term
    term: String,

    /// Output file for the graphviz representation
    #[arg(short, long("out"), default_value = "out.dot")]
    output: String,

    #[arg(short, long)]
    reductions: usize,

    #[arg(short, long, default_value = "false")]
    normalized: bool,
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
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
    let mut reducer = Reducer::new(&term, VisitOrder::LEFT_OUTERMOST);
    for _ in 0..args.reductions {
        reducer.reduce_one();
    }

    let root = if args.normalized {
        reducer.root.normalized()
    } else {
        reducer.root
    };

    std::fs::write(args.output, to_graph(&root))?;
    Ok(())
}
