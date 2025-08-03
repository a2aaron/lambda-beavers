#![feature(iter_intersperse)]
#![feature(hash_set_entry)]
#![feature(macro_metavar_expr_concat)]
#![feature(type_alias_impl_trait)]

mod common_terms;
mod debruijn;
mod graph;
mod parse_debruijn;
mod parse_term;
mod reduce;
mod replace;
mod term;

use std::time::{SystemTime, UNIX_EPOCH};

use crate::{
    common_terms::*,
    debruijn::{Debruijn, call},
    graph::{NodeIndex, ReductionGraph},
};

/// Xorshift128+ implementation stolen from tiny-rng
/// https://docs.rs/tiny-rng/
pub struct Rng {
    state: (u64, u64),
}

impl Rng {
    fn from_seed(seed: u64) -> Self {
        Self {
            state: (
                seed ^ 0xf4dbdf2183dcefb7, // [crc32(b"0"), crc32(b"1")]
                seed ^ 0x1ad5be0d6dd28e9b, // [crc32(b"2"), crc32(b"3")]
            ),
        }
    }

    fn rand_u64(&mut self) -> u64 {
        let (mut x, y) = self.state;
        self.state.0 = y;
        x ^= x << 23;
        self.state.1 = x ^ y ^ (x >> 17) ^ (y >> 26);
        self.state.1.wrapping_add(y)
    }

    fn rand_usize(&mut self) -> usize {
        self.rand_u64() as usize
    }
}

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
    for (i, node) in graph.nodes.iter().enumerate() {
        let label = node_label.to_string(node);
        let node = format!("{} [label = \"{}\"];", i, label);
        output.push(node);
    }
    for (a, b) in &graph.edges {
        let edge = format!("{} -> {}", a.0, b.0);
        output.push(edge);
    }
    output.push(format!("}}"));
    output.join("\n")
}

pub fn reduce_with_stats(graph: &mut ReductionGraph, reduction_strategy: ReductionStrategy) {
    let max = 10_000;
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
                    graph.unreduced_nodes.len(),
                    graph_update.new_nodes.len(),
                    brnf_message
                );
            }
            None => {
                assert!(graph.unreduced_nodes.is_empty());
                println!("SUCCESS, no unreduced nodes remain");
                println!(
                    "{} total nodes, {} total edges",
                    graph.nodes.len(),
                    graph.edges.len()
                );
                return;
            }
        }
    }
    println!(
        "TIMEOUT REACHED - {} unreduced nodes remain",
        graph.unreduced_nodes.len()
    );
}

pub enum ReductionStrategy {
    DFS,
    BFS,
    Random,
}

impl ReductionStrategy {
    fn get_node(&self, graph: &mut ReductionGraph) -> Option<NodeIndex> {
        if graph.unreduced_nodes.is_empty() {
            return None;
        }
        let node = match self {
            ReductionStrategy::DFS => graph.unreduced_nodes[graph.unreduced_nodes.len() - 1],
            ReductionStrategy::BFS => graph.unreduced_nodes[0],
            ReductionStrategy::Random => {
                let seed = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs();
                let mut rng = Rng::from_seed(seed);
                let index = rng.rand_usize() % graph.unreduced_nodes.len();
                graph.unreduced_nodes[index]
            }
        };
        Some(node)
    }
}

#[allow(unused_variables)]
fn main() {
    // let combined = call(call(call(PLUS(), PLUS()), CHURCH(3)), CHURCH(3));
    let combined = call(call(MULT_2(), CHURCH(5)), CHURCH(5));
    let mut graph = ReductionGraph::with_root(combined);
    reduce_with_stats(&mut graph, ReductionStrategy::Random);

    std::fs::write("out.dot", to_graphviz(&graph, NodeLabelType::BinaryLen)).unwrap();
}
