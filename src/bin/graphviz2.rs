#![feature(iter_intersperse)]

use std::{ops::ControlFlow, str::FromStr};

use clap::Parser;
use lambda_beaver::{
    debruijn::Debruijn,
    debruijn_flat::{DebruijnNode, FlatRoot, TermIndex},
    parse,
    reduce::Reducer,
    treewalk::VisitOrder,
};

fn get_garbage_array(root: &FlatRoot) -> Vec<(bool, Option<TermIndex>)> {
    let mut is_garbage = vec![(true, None); root.backing.len()];
    VisitOrder::LEFT_OUTERMOST.preorder_walk_2(root, |_, term, parent_chain| {
        let abs_bound = match root[term.term] {
            DebruijnNode::Index(index) => {
                if index <= parent_chain.len() {
                    Some(parent_chain[parent_chain.len() - index])
                } else {
                    None
                }
            }
            _ => None,
        };

        is_garbage[term.term.0] = (false, abs_bound);
        ControlFlow::Continue::<()>(())
    });

    is_garbage
}

fn to_node_label(term: DebruijnNode) -> String {
    match term {
        DebruijnNode::Index(index) => format!("idx: {index}"),
        DebruijnNode::Abstraction { usage, .. } => format!("abs\nusage = {usage}"),
        DebruijnNode::Application { .. } => format!("app"),
    }
}

const GARBAGE_COLOR: &str = "lightgrey";
const ROOT_COLOR: &str = "red";
const NORMAL_COLOR: &str = "black";

pub fn to_graph(root: &FlatRoot) -> String {
    let is_garbage = get_garbage_array(root);

    let mut output = vec![];
    output.push(format!("digraph G {{"));
    output.push("node [shape=box]".to_string());
    for (index, node) in root.backing.iter().enumerate() {
        let (is_garbage, index_bound) = is_garbage[index];
        let node_color = if is_garbage {
            GARBAGE_COLOR
        } else if index == root.root.0 {
            ROOT_COLOR
        } else {
            NORMAL_COLOR
        };

        let attribs = vec![
            ("label", to_node_label(*node)),
            ("xlabel", index.to_string()),
            ("color", node_color.to_string()),
            ("fontcolor", node_color.to_string()),
        ];

        let attribs = bake_attribs(&attribs);

        let node_text = format!("{index} [{attribs}]");
        output.push(node_text);

        let edge_color = if is_garbage {
            GARBAGE_COLOR
        } else {
            NORMAL_COLOR
        };

        let edge_attribs = format!("color={edge_color}");
        match node {
            DebruijnNode::Index(_) => {
                if let Some(abs_bound) = index_bound {
                    output.push(format!(
                        "{index} -> {abs_bound} [color=cyan, style=dashed, constraint=false]"
                    ))
                }
            }
            DebruijnNode::Abstraction { body, .. } => {
                output.push(format!("{index} -> {body} [{edge_attribs}]"))
            }
            DebruijnNode::Application { func, arg } => {
                output.push(format!("{index} -> {func} [{edge_attribs}]"));
                output.push(format!(
                    "{index} -> {arg} [{edge_attribs} arrowhead=onormal]"
                ));
            }
        };
    }
    output.push(format!("}}"));
    output.join("\n")
}

fn bake_attribs(attribs: &[(&str, String)]) -> String {
    attribs
        .iter()
        .map(|(name, value)| format!("{name}=\"{}\"", value))
        .intersperse(" ".to_string())
        .collect()
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
