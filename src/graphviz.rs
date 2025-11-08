use std::{collections::HashMap, ops::ControlFlow, process::Command};

use crate::{
    debruijn_flat::{
        BackingIndex, DebruijnEdge, DebruijnIndex, DebruijnNode, FlatRoot, RedexMut, Usage,
        compute_usage_flat,
    },
    treewalk::ActionCtx,
};
pub fn debug_write_to_file_ctx(root: &FlatRoot, ctx: &ActionCtx, name: &str) {
    _debug_write_to_file_ctx(root, Some(ctx), name);
}
pub fn debug_write_to_file(root: &FlatRoot, name: &str) {
    _debug_write_to_file_ctx(root, None, name);
}
fn _debug_write_to_file_ctx(root: &FlatRoot, ctx: Option<&ActionCtx>, name: &str) {
    let args = GraphvizArgs { no_garbage: false };
    let graph = to_graph(root, ctx, &args);
    let filename = format!("debug/{name}");
    let graphviz_file = format!("{filename}.dot");
    let image_file = format!("{filename}.png");
    std::fs::create_dir_all(format!("debug/")).unwrap();
    std::fs::write(graphviz_file.clone(), graph.to_string()).expect("Failed to write dot file");
    // dot -Tpng out.dot > out_2.png
    let command = Command::new("dot")
        .arg("-Tpng")
        .arg(graphviz_file)
        .output()
        .unwrap();
    let image_data = command.stdout;
    std::fs::write(image_file, image_data).expect("Failed to run graphviz command");
}

pub struct GraphvizArgs {
    pub no_garbage: bool,
}

pub fn to_graph(root: &FlatRoot, ctx: Option<&ActionCtx>, args: &GraphvizArgs) -> Graph {
    let mut graph = Graph::default();
    let info_vec = get_info_array(root);

    for (index, node) in root.backing.iter().enumerate() {
        let node_info = info_vec[index];

        if node_info.is_garbage && args.no_garbage {
            continue;
        }

        let mut graph_node = make_node(node, node_info);

        if ctx.is_some_and(|ctx| ctx.term == index) {
            graph_node.attribs.set("color", "green");
        }

        let mut edges = get_edges(node, node_info);

        if let Some(root_edge) = node_info.is_root {
            let mut edge = GraphvizEdge::from_debruijn_edge(root_edge, &node_info);
            // Use an invisible node to represent the "into root" edge
            let mut invis_root_attribs = Attributes::new();
            invis_root_attribs.set("style", "invis");

            let node = GraphvizNode {
                name: "invis_root".to_string(),
                attribs: invis_root_attribs,
            };
            edge.head = "invis_root".to_string();
            edges.push(edge);
            graph.nodes.push(node)
        }

        if let DebruijnNode::Application(app) = node
            && !node_info.is_garbage
        {
            let mut edge_attribs = Attributes::new();
            edge_attribs.set("style", "invis");
            let edge = GraphvizEdge::new(app.func.child, app.arg.child, &edge_attribs);
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

fn make_node(node: &DebruijnNode, node_info: NodeInfo) -> GraphvizNode {
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
    if is_abstraction {
        let bg_color = get_random_color(node_info.index, 0.5);
        attribs.set("fillcolor", bg_color).set("style", "filled");
    }

    if let Some(info) = node_info.redex_info {
        let color1 = get_random_color(info.abs.child, 0.5);
        let color2 = get_random_color(info.arg.child, 0.5);
        let bg_color = format!("{};0.5:{}", color1, color2);
        attribs
            .set("shape", "diamond")
            .set("fillcolor", bg_color)
            .set("style", "filled");
    }

    if node_info.is_root.is_some() {
        attribs.set("penwidth", 2.0);
    }

    match node_info.abs_binding {
        AbstractionBinding::NotLeaf => (),
        AbstractionBinding::BindingMissing {
            index,
            calculated_index,
        } => {
            attribs.set("fillcolor", "red").set("style", "filled");
            attribs.append_label(format!(
                "NO BINDING - raw: {}, calc: {}",
                index.get_raw(),
                calculated_index
            ));
        }
        AbstractionBinding::FreeVariable {
            calculated_index, ..
        } => attribs.append_label(format!("(free, calc: {})", calculated_index)),
        AbstractionBinding::BoundTo {
            calculated_index,
            abstraction,
            ..
        } => attribs.append_label(format!(
            "(bound @ {}, calc: {})",
            abstraction, calculated_index
        )),
    }

    if let DebruijnNode::Abstraction(abs) = *node
        && let Some(computed_usage) = node_info.computed_usage
        && abs.usage != computed_usage
    {
        attribs.set("fillcolor", "red");
        attribs.set("style", "filled");
        attribs.append_label(format!(
            "WRONG USAGE - claimed: {}, actual: {} ",
            abs.usage, computed_usage
        ));
    }

    let graph_node = GraphvizNode::new(node_info.index, &attribs);
    graph_node
}

fn get_edges(node: &DebruijnNode, node_info: NodeInfo) -> Vec<GraphvizEdge> {
    let mut edges = vec![];
    let mut edge_attribs = Attributes::new();
    edge_attribs.set("color", NORMAL_COLOR);

    if node_info.is_garbage {
        edge_attribs.set("constraint", "false");
        edge_attribs.set("color", GARBAGE_COLOR);
        edge_attribs.set("fontcolor", GARBAGE_COLOR);
    }
    match node {
        DebruijnNode::Index(_) => {
            if let AbstractionBinding::BoundTo { abstraction, .. } = node_info.abs_binding {
                let color = get_random_color(abstraction, 1.0);
                edge_attribs
                    .set("color", color)
                    .set("style", "dashed")
                    .set("constraint", "false");
                edges.push(GraphvizEdge::new(
                    node_info.index,
                    abstraction,
                    &edge_attribs,
                ));
            }
        }
        DebruijnNode::Abstraction(abs) => {
            let edge = GraphvizEdge::from_debruijn_edge(abs.body, &node_info);
            edges.push(edge);
        }
        DebruijnNode::Application(app) => {
            let edge = GraphvizEdge::from_debruijn_edge(app.func, &node_info);
            edges.push(edge);

            let mut edge = GraphvizEdge::from_debruijn_edge(app.arg, &node_info);
            edge.attributes.set("arrowhead", "onormal");
            edges.push(edge);
        }
    };
    edges
}

#[derive(Debug, Clone, Copy)]
enum AbstractionBinding {
    NotLeaf,
    BindingMissing {
        index: DebruijnIndex,
        calculated_index: usize,
    },
    FreeVariable {
        calculated_index: usize,
    },
    BoundTo {
        calculated_index: usize,
        abstraction: BackingIndex,
    },
}

#[derive(Debug, Clone, Copy)]
struct NodeInfo {
    is_root: Option<DebruijnEdge>,
    index: usize,
    // If true, the this DebruijNode is garbage
    is_garbage: bool,
    // If not None, then this DebruijNode is a non-garbage Index node
    // and the value of this field is equal to the non-garbage Abstraction node that this
    // Index node binds to.
    // Note that a DebruijnNode can be an Index node without this field being set (which happens if
    // the Index node is garbage or if the Index node is unbound within the whole term)
    abs_binding: AbstractionBinding,
    // If not None, then this DebruijnNode is an non-garbage Application and is also a Redex
    redex_info: Option<RedexInfo>,
    computed_usage: Option<Usage>,
}

impl NodeInfo {
    fn garbage(index: usize) -> NodeInfo {
        NodeInfo {
            index,
            is_root: None,
            is_garbage: true,
            abs_binding: AbstractionBinding::NotLeaf,
            redex_info: None,
            computed_usage: None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct RedexInfo {
    // The function of the application in the redex, which will be an Abstraction
    abs: DebruijnEdge,
    // The argument of the application in the redex
    arg: DebruijnEdge,
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
                let (calculated_index, err) = index.get_failable(&ctx.chain);
                if let Some(err) = err {
                    println!("{err}")
                }
                if calculated_index <= depth {
                    match chain.abstractions.get(depth - calculated_index) {
                        Some(&abstraction) => AbstractionBinding::BoundTo {
                            calculated_index,
                            abstraction: abstraction.parent_index().unwrap(),
                        },
                        None => AbstractionBinding::BindingMissing {
                            index,
                            calculated_index,
                        },
                    }
                } else {
                    AbstractionBinding::FreeVariable { calculated_index }
                }
            }
            _ => AbstractionBinding::NotLeaf,
        };

        let redex_info = match RedexMut::try_get(root, ctx) {
            Some(redex) => Some(RedexInfo {
                abs: redex.app_to_abs,
                arg: redex.app_to_arg,
            }),
            None => None,
        };

        let is_root = root.root.child == ctx.term;

        let index = ctx.term;
        info_vec[index].is_root = if is_root { Some(root.root) } else { None };
        info_vec[index].is_garbage = false;
        info_vec[index].abs_binding = abs_bound;
        info_vec[index].redex_info = redex_info;

        if matches!(root[ctx.term], DebruijnNode::Abstraction(_)) {
            info_vec[index].computed_usage = Some(compute_usage_flat(root, ctx));
        }
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

    fn get(&self, key: &str) -> Option<&String> {
        self.attributes.get(key)
    }

    fn append_label(&mut self, str: impl ToString) {
        let label = self.get("label");
        if let Some(label) = label {
            let label = format!("{label}\n{}", str.to_string());
            self.set("label", label);
        } else {
            self.set("label", str);
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq, Clone)]
pub struct Graph {
    name: String,
    nodes: Vec<GraphvizNode>,
    edges: Vec<GraphvizEdge>,
    subgraphs: Vec<Graph>,
    attribs: Attributes,
}

impl Graph {
    pub fn to_string(&self) -> String {
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

        for GraphvizEdge {
            head,
            tail,
            attributes: attribs,
        } in &self.edges
        {
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
struct GraphvizNode {
    name: String,
    attribs: Attributes,
}
impl GraphvizNode {
    fn new(name: usize, attributes: &Attributes) -> GraphvizNode {
        GraphvizNode {
            name: name.to_string(),
            attribs: attributes.clone(),
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq, Clone)]
struct GraphvizEdge {
    head: String,
    tail: String,
    attributes: Attributes,
}
impl GraphvizEdge {
    fn new(head: usize, tail: usize, attributes: &Attributes) -> GraphvizEdge {
        GraphvizEdge {
            head: head.to_string(),
            tail: tail.to_string(),
            attributes: attributes.clone(),
        }
    }

    fn from_debruijn_edge(edge: DebruijnEdge, node_info: &NodeInfo) -> GraphvizEdge {
        let mut attributes = Attributes::new();
        attributes.set("color", NORMAL_COLOR);

        if node_info.is_garbage {
            // attributes.set("constraint", "false");
            attributes.set("color", GARBAGE_COLOR);
            attributes.set("fontcolor", GARBAGE_COLOR);
        }

        if let Some(adjust) = edge.adjust {
            attributes.set("penwidth", "5");
            attributes.set("label", format!("adj = {adjust}"));
        }

        let head = node_info.index;
        let tail = edge.child;
        GraphvizEdge::new(head, tail, &attributes)
    }
}

fn get_random_color(term: usize, saturation: f32) -> String {
    // Divide by phi here to get reasonably 'random' colors
    let hue = (term as f32 / std::f32::consts::PHI).fract();
    format!("{hue} {saturation} 0.75")
}
