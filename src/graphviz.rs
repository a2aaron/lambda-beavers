use std::{
    collections::HashMap,
    process::Command,
    sync::{
        LazyLock,
        atomic::{AtomicBool, AtomicUsize, Ordering},
    },
    time::SystemTime,
};

use crate::{
    debruijn_flat::{
        BackingIndex, Binding, DebruijnNode, DoubleEndedEdge, FlatTree, Usage, compute_usage_flat,
    },
    treewalk::ActionCtx,
};

const DEBUG: bool = true;

static CURRENTLY_WRITING_GRAPH: AtomicBool = AtomicBool::new(false);

static COUNTER: AtomicUsize = AtomicUsize::new(0);
static TIMESTAMP: LazyLock<u64> = LazyLock::new(|| {
    SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap()
        .as_secs()
});

pub fn debug_write_to_file_ctx(tree: &FlatTree, ctx: &ActionCtx, name: &str) {
    _debug_write_to_file_ctx(tree, Some(ctx), name);
}
pub fn debug_write_to_file(tree: &FlatTree, name: &str) {
    _debug_write_to_file_ctx(tree, None, name);
}
fn _debug_write_to_file_ctx(tree: &FlatTree, ctx: Option<&ActionCtx>, name: &str) {
    if !DEBUG {
        return;
    }

    if CURRENTLY_WRITING_GRAPH.load(Ordering::Relaxed) {
        println!("Not writing graph for {name} because one is already in progress...");
        println!("{}", std::backtrace::Backtrace::force_capture());
        return;
    }
    CURRENTLY_WRITING_GRAPH.store(true, Ordering::Relaxed);
    let value = COUNTER.fetch_add(1, Ordering::Relaxed);

    let args = GraphvizArgs { no_garbage: false };
    let graph = to_graph(tree, ctx, &args);

    let timestamp = *TIMESTAMP;
    let folder = &format!("debug/{timestamp}");
    std::fs::create_dir_all(folder).unwrap();

    let graphviz_file = format!("{folder}/_{value}_{name}.dot");
    let image_file = format!("{folder}/{value}_{name}.png");
    std::fs::write(graphviz_file.clone(), graph.to_string()).expect("Failed to write dot file");
    // dot -Tpng out.dot > out_2.png
    let command = Command::new("dot")
        .arg("-Tpng")
        .arg(graphviz_file)
        .output()
        .unwrap();
    let image_data = command.stdout;
    std::fs::write(image_file, image_data).expect("Failed to run graphviz command");

    CURRENTLY_WRITING_GRAPH.store(false, Ordering::Relaxed);
}

pub struct GraphvizArgs {
    pub no_garbage: bool,
}

pub fn to_graph(tree: &FlatTree, ctx: Option<&ActionCtx>, args: &GraphvizArgs) -> Graph {
    let mut graph = Graph::default();
    let info_vec = get_info_array(tree);

    for node_info in info_vec {
        if node_info.is_garbage && args.no_garbage {
            continue;
        }

        process_node(&mut graph, node_info);
    }

    if let Some(ctx) = ctx {
        for edge in &ctx.chain.full_chain {
            update_or_add_ctx_edge(&mut graph, *edge);
        }
    }
    graph
}

fn update_or_add_ctx_edge(graph: &mut Graph, edge: DoubleEndedEdge) {
    let start = edge.edge_w_parent.backing_index();
    let end = edge.child;

    let start = match start {
        Some(parent) => parent.to_string(),
        None => INTO_ROOT.to_string(),
    };
    let end = end.to_string();

    let ok = graph.get_edge(&start, &end).is_some();

    let mut attributes = Attributes::new();
    attributes.set("style", "dotted");
    attributes.set("constraint", "false");

    if ok {
        attributes.set("color", "green");
        attributes.set("fontcolor", "green");
    } else {
        attributes.set("color", "red");
        attributes.set("fontcolor", "red");
    }

    let edge = GraphvizEdge {
        start,
        end,
        attributes,
    };
    graph.edges.push(edge);
}

fn process_node(graph: &mut Graph, node_info: NodeInfo) {
    let graph_node = make_node(node_info);

    let mut edges = get_edges(node_info);

    if let Some(root_edge) = node_info.is_root {
        let (edge, node) = make_into_root_edge(node_info, root_edge);
        edges.push(edge);
        graph.nodes.push(node)
    }

    if let DebruijnNode::Application(app) = node_info.node
        && !node_info.is_garbage
    {
        add_subgraph_for_application_edge(graph, app);
    }

    graph.nodes.push(graph_node);
    graph.edges.append(&mut edges);
}

fn make_into_root_edge(node_info: NodeInfo, root: BackingIndex) -> (GraphvizEdge, GraphvizNode) {
    // Use an invisible node to represent the "into root" edge
    let mut invis_root_attribs = Attributes::new();
    invis_root_attribs.set("style", "invis");

    let node = GraphvizNode {
        name: INTO_ROOT.to_string(),
        attributes: invis_root_attribs,
    };

    let mut edge = GraphvizEdge::make_normal_edge(&node_info, root);
    edge.start = INTO_ROOT.to_string();

    (edge, node)
}

fn add_subgraph_for_application_edge(graph: &mut Graph, app: crate::debruijn_flat::Application) {
    let mut edge_attribs = Attributes::new();
    edge_attribs.set("style", "invis");
    let edge = GraphvizEdge::new(app.func, app.arg, &edge_attribs);
    let mut same_rank = Graph::default();
    same_rank.edges.push(edge);
    same_rank.attribs.set("rank", "same");
    same_rank.attribs.set("rankdir", "LR");
    graph.subgraphs.push(same_rank);
}

fn make_node(node_info: NodeInfo) -> GraphvizNode {
    let mut attributes = Attributes::new();
    // Set basic info
    attributes
        .set("label", to_node_label(node_info.node))
        .set("xlabel", node_info.index.0)
        .set("color", NORMAL_COLOR)
        .set("fontcolor", NORMAL_COLOR);

    // Set color for garbage
    if node_info.is_garbage {
        attributes
            .set("color", GARBAGE_COLOR)
            .set("fontcolor", GARBAGE_COLOR);
    }

    // Set color for abstraction
    let is_abstraction = matches!(node_info.node, DebruijnNode::Abstraction(_));
    if is_abstraction {
        let bg_color = get_random_color(node_info.index, 0.5);
        attributes.set("fillcolor", bg_color).set("style", "filled");
    }

    // Set shape and color for redex application
    if let Some(info) = node_info.redex_info {
        let color1 = get_random_color(info.abs, 0.5);
        let color2 = get_random_color(info.arg, 0.5);
        let bg_color = format!("{};0.5:{}", color1, color2);
        attributes
            .set("shape", "diamond")
            .set("fillcolor", bg_color)
            .set("style", "filled");
    }

    if node_info.is_root.is_some() {
        attributes.set("penwidth", 2.0);
    }

    // Usage mismatch between claimed and actual usage
    // Note that garbage nodes are allowed to have stale usage amounts
    if let DebruijnNode::Abstraction(abs) = node_info.node
        && let Some(computed_usage) = node_info.computed_usage
        && abs.usage != computed_usage
        && !node_info.is_garbage
    {
        attributes.set("color", "red");
        attributes.set("fontcolor", "darkred");
        attributes.set("style", "filled");
        attributes.append_label(format!(
            "WRONG USAGE\nclaimed: {}, actual: {} ",
            abs.usage, computed_usage
        ));
    }

    let graph_node = GraphvizNode::new(node_info.index, attributes);
    graph_node
}

fn get_edges(node_info: NodeInfo) -> Vec<GraphvizEdge> {
    let mut edges = vec![];
    match node_info.node {
        DebruijnNode::Index(binding) => {
            // Add binding edge
            if let Binding::Bound(abstraction) = binding {
                let binding_edge = GraphvizEdge::make_binding_edge(node_info.index, abstraction);
                edges.push(binding_edge);
            }
        }
        // Add normal edges
        DebruijnNode::Abstraction(abs) => {
            let edge = GraphvizEdge::make_normal_edge(&node_info, abs.body);
            edges.push(edge);
        }
        DebruijnNode::Application(app) => {
            let edge = GraphvizEdge::make_normal_edge(&node_info, app.func);
            edges.push(edge);

            let mut edge = GraphvizEdge::make_normal_edge(&node_info, app.arg);
            edge.attributes.set("arrowhead", "onormal");
            edges.push(edge);
        }
    };
    edges
}

#[derive(Debug, Clone, Copy)]
struct NodeInfo {
    node: DebruijnNode,
    is_root: Option<BackingIndex>,
    // Backing index of the node
    index: BackingIndex,
    // If true, the this DebruijNode is garbage
    is_garbage: bool,
    // If not None, then this DebruijnNode is an non-garbage Application and is also a Redex
    redex_info: Option<RedexInfo>,
    computed_usage: Option<Usage>,
}

impl NodeInfo {
    fn garbage(root: &FlatTree, index: BackingIndex) -> NodeInfo {
        let node = root[index];
        NodeInfo {
            node,
            index,
            is_root: None,
            is_garbage: true,
            redex_info: None,
            computed_usage: None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct RedexInfo {
    // The function of the application in the redex, which will be an Abstraction
    abs: BackingIndex,
    // The argument of the application in the redex
    arg: BackingIndex,
}

fn get_info_array(tree: &FlatTree) -> Vec<NodeInfo> {
    let mut info_vec: Vec<NodeInfo> = (0..tree.backing.len())
        .map(|index| NodeInfo::garbage(tree, BackingIndex(index)))
        .collect();

    let redexes = tree.get_redexes();
    let non_garbage = get_non_garbage(tree);

    for (index, node) in tree.backing.iter().enumerate() {
        info_vec[index].is_garbage = !non_garbage.contains(&BackingIndex(index));

        let is_root = tree.root.0 == index;
        info_vec[index].is_root = if is_root { Some(tree.root) } else { None };

        let redex_info = redexes
            .iter()
            .find(|redex| redex.app_index.0 == index)
            .map(|redex| RedexInfo {
                abs: redex.func_index,
                arg: redex.arg_index,
            });
        info_vec[index].redex_info = redex_info;

        if matches!(node, DebruijnNode::Abstraction(_)) {
            info_vec[index].computed_usage = Some(compute_usage_flat(tree, BackingIndex(index)));
        }
    }

    info_vec
}

fn get_non_garbage(tree: &FlatTree) -> Vec<BackingIndex> {
    fn _get_non_garbage(tree: &FlatTree, non_garbage: &mut Vec<BackingIndex>, index: BackingIndex) {
        non_garbage.push(index);
        match tree[index] {
            DebruijnNode::Index(_) => (),
            DebruijnNode::Abstraction(abstraction) => {
                _get_non_garbage(tree, non_garbage, abstraction.body)
            }
            DebruijnNode::Application(application) => {
                _get_non_garbage(tree, non_garbage, application.func);
                _get_non_garbage(tree, non_garbage, application.arg);
            }
        }
    }
    let mut non_garbage = vec![];
    _get_non_garbage(tree, &mut non_garbage, tree.root);
    non_garbage
}

fn to_node_label(term: DebruijnNode) -> String {
    match term {
        DebruijnNode::Index(index) => format!("idx: {}", index),
        DebruijnNode::Abstraction(abs) => format!("abs\nusage = {}", abs.usage),
        DebruijnNode::Application { .. } => format!("app"),
    }
}

const INTO_ROOT: &str = "into_root";

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
            output.push(format!("{} [{}]", node.name, node.attributes.bake()))
        }

        for GraphvizEdge {
            start,
            end,
            attributes,
        } in &self.edges
        {
            let attributes = &attributes.bake();
            output.push(format!("{start} -> {end} [{attributes}]"));
        }

        for graph in &self.subgraphs {
            output.push(graph.print_graph(""));
        }

        output.push(format!("}}"));
        output.join("\n")
    }

    fn get_edge(&mut self, start: &str, end: &str) -> Option<&mut GraphvizEdge> {
        self.edges
            .iter_mut()
            .find(|edge| edge.start == start && edge.end == end)
    }
}

#[derive(Debug, Default, PartialEq, Eq, Clone)]
struct GraphvizNode {
    name: String,
    attributes: Attributes,
}
impl GraphvizNode {
    fn new(index: BackingIndex, attributes: Attributes) -> GraphvizNode {
        GraphvizNode {
            name: index.0.to_string(),
            attributes,
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq, Clone)]
struct GraphvizEdge {
    start: String,
    end: String,
    attributes: Attributes,
}
impl GraphvizEdge {
    fn new(start: BackingIndex, end: BackingIndex, attributes: &Attributes) -> GraphvizEdge {
        GraphvizEdge {
            start: start.0.to_string(),
            end: end.0.to_string(),
            attributes: attributes.clone(),
        }
    }

    fn make_binding_edge(index: BackingIndex, abstraction: BackingIndex) -> GraphvizEdge {
        let color = get_random_color(abstraction, 1.0);
        let mut edge_attribs = Attributes::new();
        edge_attribs
            .set("color", color)
            .set("style", "dashed")
            .set("constraint", "false");
        GraphvizEdge::new(index, abstraction, &edge_attribs)
    }

    fn make_normal_edge(node_info: &NodeInfo, end: BackingIndex) -> GraphvizEdge {
        let start = node_info.index;

        let mut attributes = Attributes::new();
        attributes.set("color", NORMAL_COLOR);

        // Grey out edge if it is part of garbage
        if node_info.is_garbage {
            // attributes.set("constraint", "false");
            attributes.set("color", GARBAGE_COLOR);
            attributes.set("fontcolor", GARBAGE_COLOR);
        }

        GraphvizEdge::new(start, end, &attributes)
    }
}

fn get_random_color(term: BackingIndex, saturation: f32) -> String {
    // Divide by phi here to get reasonably 'random' colors
    let hue = (term.0 as f32 / std::f32::consts::PHI).fract();
    format!("{hue} {saturation} 0.75")
}
