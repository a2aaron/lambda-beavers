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
    VisitOrder::LEFT_OUTERMOST.preorder_walk(root, |_, term, parent_chain| {
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
        DebruijnNode::Abstraction(abs) => format!("abs\nusage = {}", abs.usage),
        DebruijnNode::Application { .. } => format!("app"),
    }
}

const GARBAGE_COLOR: &str = "lightgrey";
const NORMAL_COLOR: &str = "black";

type Attributes = Vec<(&'static str, String)>;
type Edge = (usize, usize, Attributes);

pub fn to_graph(root: &FlatRoot) -> String {
    let is_garbage = get_garbage_array(root);

    let mut output = vec![];
    output.push(format!("digraph G {{"));
    output.push("node [shape=box]".to_string());
    for (index, node) in root.backing.iter().enumerate() {
        let (is_garbage, index_bound) = is_garbage[index];
        let node_color = if is_garbage {
            GARBAGE_COLOR.to_string()
        } else {
            NORMAL_COLOR.to_string()
        };

        let bg_color = if let DebruijnNode::Abstraction(_) = node {
            get_random_color(index, 0.5)
        } else {
            "white".to_string()
        };

        let mut attribs: Attributes = vec![
            ("label", to_node_label(*node)),
            ("xlabel", index.to_string()),
            ("color", node_color.to_string()),
            ("fillcolor", bg_color.to_string()),
            ("style", "filled".to_string()),
            ("fontcolor", node_color.to_string()),
        ];

        if index == root.root.0 {
            attribs.push(("penwidth", "2.0".to_string()));
        }

        let attribs = bake_attribs(&attribs);

        let node_text = format!("{index} [{attribs}]");
        output.push(node_text);

        let edge_color = if is_garbage {
            GARBAGE_COLOR
        } else {
            NORMAL_COLOR
        };

        let mut edges: Vec<Edge> = vec![];
        match node {
            DebruijnNode::Index(_) => {
                if let Some(abs_bound) = index_bound {
                    let color = get_random_color(abs_bound.0, 1.0);
                    let edge_attribs: Attributes = vec![
                        ("color", color),
                        ("style", "dashed".to_string()),
                        ("constraint", "false".to_string()),
                    ];
                    edges.push((index, abs_bound.0, edge_attribs));
                }
            }
            DebruijnNode::Abstraction(abs) => {
                let edge_attribs: Attributes = vec![("color", edge_color.to_string())];
                let body = abs.body.0;
                edges.push((index, body, edge_attribs));
            }
            DebruijnNode::Application(app) => {
                let mut edge_attribs: Attributes = vec![("color", edge_color.to_string())];

                let func = app.func.0;
                let arg = app.arg.0;
                edges.push((index, func, edge_attribs.clone()));

                edge_attribs.push(("arrowhead", "onormal".to_string()));
                edges.push((index, arg, edge_attribs));
            }
        };

        for (head, tail, attribs) in edges {
            let attribs = bake_attribs(&attribs);
            output.push(format!("{head} -> {tail} [{attribs}]"));
        }
    }
    output.push(format!("}}"));
    output.join("\n")
}

fn get_random_color(term: usize, saturation: f32) -> String {
    let hue = f32::sin(term as f32).abs();
    format!("{hue} {saturation} 1.0")
}

fn bake_attribs(attribs: &Attributes) -> String {
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
