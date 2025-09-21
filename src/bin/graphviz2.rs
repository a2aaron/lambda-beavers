#![feature(iter_intersperse)]

use std::{collections::HashMap, ops::ControlFlow, str::FromStr};

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

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct Attributes {
    attributes: HashMap<String, String>,
}
impl Attributes {
    fn new() -> Attributes {
        Attributes {
            ..Default::default()
        }
    }

    fn set(&mut self, value: impl ToString, key: impl ToString) -> &mut Attributes {
        self.attributes.insert(value.to_string(), key.to_string());
        self
    }

    fn bake(&self) -> String {
        self.attributes
            .iter()
            .map(|(name, value)| format!("{name}=\"{}\"", value))
            .intersperse(" ".to_string())
            .collect()
    }
}

type Edge = (usize, usize, Attributes);

pub fn to_graph(root: &FlatRoot, args: &Args) -> String {
    let is_garbage = get_garbage_array(root);

    let mut output = vec![];
    output.push(format!("digraph G {{"));
    output.push("node [shape=box]".to_string());
    for (index, node) in root.backing.iter().enumerate() {
        let (is_garbage, index_bound) = is_garbage[index];

        if is_garbage && args.no_garbage {
            continue;
        }

        let mut attribs = Attributes::new();
        attribs
            .set("label", to_node_label(*node))
            .set("xlabel", index)
            .set("color", NORMAL_COLOR)
            .set("fontcolor", NORMAL_COLOR);

        if is_garbage {
            attribs
                .set("color", GARBAGE_COLOR)
                .set("fontcolor", GARBAGE_COLOR);
        } else if let DebruijnNode::Abstraction(_) = node
            && !args.no_color_abs
        {
            let bg_color = get_random_color(index, 0.5);
            attribs.set("fillcolor", bg_color).set("style", "filled");
        }

        if index == root.root.0 {
            attribs.set("penwidth", 2.0);
        }

        let attribs = attribs.bake();
        let node_text = format!("{index} [{attribs}]");
        output.push(node_text);

        let edge_color = if is_garbage {
            GARBAGE_COLOR
        } else {
            NORMAL_COLOR
        };

        let mut edge_attribs = Attributes::new();
        edge_attribs.set("color", edge_color);

        let mut edges: Vec<Edge> = vec![];
        match node {
            DebruijnNode::Index(_) => {
                if let Some(abs_bound) = index_bound
                    && !args.no_color_abs
                {
                    let color = get_random_color(abs_bound.0, 1.0);
                    let edge_attribs = edge_attribs
                        .set("color", color)
                        .set("style", "dashed")
                        .set("constraint", "false");
                    edges.push((index, abs_bound.0, edge_attribs.clone()));
                }
            }
            DebruijnNode::Abstraction(abs) => {
                let body = abs.body.0;
                edges.push((index, body, edge_attribs.clone()));
            }
            DebruijnNode::Application(app) => {
                let func = app.func.0;
                let arg = app.arg.0;
                edges.push((index, func, edge_attribs.clone()));

                let edge_attribs = edge_attribs.set("arrowhead", "onormal");
                edges.push((index, arg, edge_attribs.clone()));
            }
        };

        for (head, tail, attribs) in edges {
            let attribs = &attribs.bake();
            output.push(format!("{head} -> {tail} [{attribs}]"));
        }
    }
    output.push(format!("}}"));
    output.join("\n")
}

fn get_random_color(term: usize, saturation: f32) -> String {
    let hue = f32::sin(term as f32 * 0.98).abs();
    format!("{hue} {saturation} 1.0")
}

#[derive(Parser, Debug)]
#[command(about, long_about = None)]
pub struct Args {
    /// Term to parse. This can be a classic or Debruijn term
    term: String,

    /// Output file for the graphviz representation
    #[arg(short, long("out"), default_value = "out.dot")]
    output: String,

    #[arg(short, long)]
    reductions: usize,

    #[arg(short, long, default_value = "false")]
    normalized: bool,

    #[arg(short, long, default_value = "false")]
    no_garbage: bool,

    #[arg(short, long, default_value = "false")]
    no_color_abs: bool,
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    let term = args.term.clone();
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

    std::fs::write(args.output.clone(), to_graph(&root, &args))?;
    Ok(())
}
