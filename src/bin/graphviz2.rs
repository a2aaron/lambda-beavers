#![feature(iter_intersperse)]
#![feature(more_float_constants)]

use core::f32;
use std::{collections::HashMap, ops::ControlFlow, str::FromStr};

use clap::Parser;
use lambda_beaver::{
    debruijn::Debruijn,
    debruijn_flat::{DebruijnNode, FlatRoot, RedexMut, TermIndex},
    parse,
    reduce::Reducer,
};

#[derive(Debug, Clone, Copy)]
struct NodeInfo {
    is_root: bool,
    index: usize,
    // If true, the this DebruijNode is garbage
    is_garbage: bool,
    // If not None, then this DebruijNode is a non-garbage Index node
    // and the value of this field is equal to the non-garbage Abstraction node that this
    // Index node binds to.
    // Note that a DebruijnNode can be an Index node without this field being set (which happens if
    // the Index node is garbage or if the Index node is unbound within the whole term)
    abs_binding: Option<TermIndex>,
    // If not None, then this DebruijnNode is an non-garbage Application and is also a Redex
    redex_info: Option<RedexInfo>,
}

impl NodeInfo {
    fn garbage(index: usize) -> NodeInfo {
        NodeInfo {
            index,
            is_root: false,
            is_garbage: true,
            abs_binding: None,
            redex_info: None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct RedexInfo {
    // The function of the application in the redex, which will be an Abstraction
    abs: TermIndex,
    // The argument of the application in the redex
    arg: TermIndex,
}

fn get_info_array(root: &FlatRoot) -> Vec<NodeInfo> {
    let mut info_vec: Vec<NodeInfo> = (0..root.backing.len())
        .map(|index| NodeInfo::garbage(index))
        .collect();
    root.preorder_walk(|root, ctx| {
        let abs_bound = match root[ctx.term] {
            DebruijnNode::Index(index) => {
                let chain = &ctx.chain;
                let depth = ctx.chain.debruijn_depth();
                if index.get(chain) <= depth {
                    Some(chain.abstractions[depth - index.get(chain)])
                } else {
                    None
                }
            }
            _ => None,
        };

        let redex_info = match RedexMut::try_get(root, ctx) {
            Some(redex) => Some(RedexInfo {
                abs: redex.abs,
                arg: redex.arg,
            }),
            None => None,
        };

        let is_root = root.root == ctx.term.term;

        let index = ctx.term.term.index;
        info_vec[index].is_root = is_root;
        info_vec[index].is_garbage = false;
        info_vec[index].abs_binding = abs_bound;
        info_vec[index].redex_info = redex_info;
        ControlFlow::Continue::<()>(())
    });

    info_vec
}

fn to_node_label(term: DebruijnNode) -> String {
    match term {
        DebruijnNode::Index(index) => format!("idx: {}", index.get_raw()),
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

#[derive(Debug, Default, PartialEq, Eq, Clone)]
struct Graph {
    name: String,
    nodes: Vec<Node>,
    edges: Vec<Edge>,
    subgraphs: Vec<Graph>,
    attribs: Attributes,
}

impl Graph {
    fn to_string(&self) -> String {
        self.print_graph("digraph")
    }
    fn print_graph(&self, keyword: &str) -> String {
        let mut output = vec![];
        output.push(format!("{keyword} {} {{", self.name));
        for (key, value) in self.attribs.attributes.iter() {
            output.push(format!("{key} = \"{value}\";"));
        }
        output.push("node [shape=box]".to_string());

        for node in &self.nodes {
            output.push(format!("{} [{}]", node.name, node.attribs.bake()))
        }

        for Edge(head, tail, attribs) in &self.edges {
            let attribs = &attribs.bake();
            output.push(format!("{head} -> {tail} [{attribs}]"));
        }

        for graph in &self.subgraphs {
            output.push(graph.print_graph(""));
        }

        output.push(format!("}}"));
        output.join("\n")
    }
}

#[derive(Debug, Default, PartialEq, Eq, Clone)]
struct Node {
    name: String,
    attribs: Attributes,
}
impl Node {
    fn new(name: usize, attributes: &Attributes) -> Node {
        Node {
            name: name.to_string(),
            attribs: attributes.clone(),
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq, Clone)]
struct Edge(String, String, Attributes);
impl Edge {
    fn new(head: usize, tail: usize, attributes: &Attributes) -> Edge {
        Edge(head.to_string(), tail.to_string(), attributes.clone())
    }
}

fn to_graph(root: &FlatRoot, args: &Args) -> Graph {
    let mut graph = Graph::default();
    let info_vec = get_info_array(root);

    for (index, node) in root.backing.iter().enumerate() {
        let node_info = info_vec[index];

        if node_info.is_garbage && args.no_garbage {
            continue;
        }

        let graph_node = make_node(args, node, node_info);
        let mut edges = get_edges(args, node, node_info);

        if let DebruijnNode::Application(app) = node
            && !node_info.is_garbage
        {
            let mut edge_attribs = Attributes::new();
            edge_attribs.set("style", "invis");
            let edge = Edge::new(app.func.index, app.arg.index, &edge_attribs);
            let mut same_rank = Graph::default();
            same_rank.edges.push(edge);
            same_rank.attribs.set("rank", "same");
            same_rank.attribs.set("rankdir", "LR");
            graph.subgraphs.push(same_rank);
        }

        graph.nodes.push(graph_node);
        graph.edges.append(&mut edges);
    }
    graph
}

fn get_edges(args: &Args, node: &DebruijnNode, node_info: NodeInfo) -> Vec<Edge> {
    let mut edges = vec![];
    let mut edge_attribs = Attributes::new();
    edge_attribs.set(
        "color",
        if node_info.is_garbage {
            GARBAGE_COLOR
        } else {
            NORMAL_COLOR
        },
    );
    match node {
        DebruijnNode::Index(_) => {
            if let Some(abs_bound) = node_info.abs_binding
                && !args.no_color_abs
            {
                let color = get_random_color(abs_bound.index, 1.0);
                edge_attribs
                    .set("color", color)
                    .set("style", "dashed")
                    .set("constraint", "false");
                edges.push(Edge::new(node_info.index, abs_bound.index, &edge_attribs));
            }
        }
        DebruijnNode::Abstraction(abs) => {
            let body = abs.body.index;
            add_if_subterm_termindex(&mut edge_attribs, abs.body);
            edges.push(Edge::new(node_info.index, body, &edge_attribs));
        }
        DebruijnNode::Application(app) => {
            let func = app.func.index;
            let arg = app.arg.index;

            let mut func_attribs = edge_attribs.clone();
            add_if_subterm_termindex(&mut func_attribs, app.func);
            edges.push(Edge::new(node_info.index, func, &func_attribs));

            let mut arg_attribs = edge_attribs.clone();
            add_if_subterm_termindex(&mut arg_attribs, app.arg);
            arg_attribs.set("arrowhead", "onormal");
            edges.push(Edge::new(node_info.index, arg, &arg_attribs));
        }
    };
    edges
}

fn add_if_subterm_termindex(edge_attribs: &mut Attributes, term: TermIndex) {
    if term.subterm_adjust.is_some() {
        edge_attribs.set("penwidth", "5");
    }
}

fn make_node(args: &Args, node: &DebruijnNode, node_info: NodeInfo) -> Node {
    let mut attribs = Attributes::new();
    attribs
        .set("label", to_node_label(*node))
        .set("xlabel", node_info.index)
        .set("color", NORMAL_COLOR)
        .set("fontcolor", NORMAL_COLOR);

    if node_info.is_garbage {
        attribs
            .set("color", GARBAGE_COLOR)
            .set("fontcolor", GARBAGE_COLOR);
    }

    let is_abstraction = matches!(node, DebruijnNode::Abstraction(_));
    if is_abstraction && !args.no_color_abs {
        let bg_color = get_random_color(node_info.index, 0.5);
        attribs.set("fillcolor", bg_color).set("style", "filled");
    }

    if let Some(info) = node_info.redex_info
        && !args.no_color_redex
    {
        let color1 = get_random_color(info.abs.index, 0.5);
        let color2 = get_random_color(info.arg.index, 0.5);
        let bg_color = format!("{};0.5:{}", color1, color2);
        attribs
            .set("shape", "diamond")
            .set("fillcolor", bg_color)
            .set("style", "filled");
    }

    if node_info.is_root {
        attribs.set("penwidth", 2.0);
    }

    let graph_node = Node::new(node_info.index, &attribs);
    graph_node
}

fn get_random_color(term: usize, saturation: f32) -> String {
    // Divide by phi here to get reasonably 'random' colors
    let hue = (term as f32 / f32::consts::PHI).fract();
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

    #[arg(short, long, default_value = "false")]
    no_color_redex: bool,
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
    let mut reducer = Reducer::new(&term);
    for _ in 0..args.reductions {
        reducer.reduce_one();
    }

    let root = if args.normalized {
        reducer.root.normalized()
    } else {
        reducer.root
    };

    let graph = to_graph(&root, &args);
    std::fs::write(args.output.clone(), graph.to_string())?;
    Ok(())
}
