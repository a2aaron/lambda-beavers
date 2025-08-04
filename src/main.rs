#![feature(iter_intersperse)]
#![feature(hash_set_entry)]
#![feature(macro_metavar_expr_concat)]
#![feature(type_alias_impl_trait)]
#![feature(never_type)]

mod common_terms;
mod debruijn;
mod graph;
mod parse_binary;
mod parse_debruijn;
mod parse_term;
mod reduce;
mod replace;
mod term;

use std::time::{SystemTime, UNIX_EPOCH};

use crate::{
    common_terms::{CHURCH, MULT},
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

pub fn reduce_with_stats(
    graph: &mut ReductionGraph,
    reduction_strategy: ReductionStrategy,
    max: usize,
) {
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

pub fn reduce(
    graph: &mut ReductionGraph,
    reduction_strategy: ReductionStrategy,
    max: usize,
) -> Option<(Debruijn, usize)> {
    for i in 0..max {
        let node_to_reduce = reduction_strategy.get_node(graph);
        match node_to_reduce {
            Some(node_to_reduce) => {
                let graph_update = graph.reduce_node(node_to_reduce);
                if graph_update.is_brnf {
                    let reduced_term = graph.get(node_to_reduce).unwrap();
                    return Some((reduced_term, i));
                }
            }
            _ => (),
        }
    }
    None
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

pub fn bitstring_permutations(n: usize) -> impl Iterator<Item = Vec<bool>> {
    let two_pow_n = 1 << n;
    (0..two_pow_n).map(move |value| {
        // note: we want the first bool in the array to represent the high order bit
        // so we must iterate the bits in reverse order
        (0..n)
            .rev()
            .map(|bit_to_extract| {
                let extracted_bit = value >> bit_to_extract;
                let bottom_bit_is_one = (extracted_bit & 1) != 0;
                bottom_bit_is_one
            })
            .collect()
    })
}

#[allow(unused_variables)]
fn main() {
    // for length in 0..16 {
    //     let terms = bitstring_permutations(length)
    //         .filter_map(|bitstring| parse_binary::from_vec(bitstring.to_vec()).ok());

    //     for term in terms {
    //         let mut graph = ReductionGraph::with_root(term.clone());
    //         let brnf = reduce(&mut graph, ReductionStrategy::DFS, 10_000);
    //         if let Some((brnf, reductions_used)) = brnf {
    //             let binary_term = format!("{:b}", term);
    //             let binary_brnf = format!("{:b}", brnf);
    //             println!(
    //                 "{} -> {} | {} -> {} | lengths: {} -> {} | found in {}",
    //                 binary_term,
    //                 binary_brnf,
    //                 term,
    //                 brnf,
    //                 binary_term.len(),
    //                 binary_brnf.len(),
    //                 reductions_used
    //             );
    //         } else {
    //             println!(
    //                 "{:b} [{}] -> <not found after 10000 reductions>",
    //                 term, term
    //             );
    //         }
    //     }
    // }

    let term = call(call(MULT(), CHURCH(5)), CHURCH(3));
    let mut graph = ReductionGraph::with_root(term);
    reduce(&mut graph, ReductionStrategy::DFS, 1000000);
    std::fs::write("out.dot", to_graphviz(&graph, NodeLabelType::Debruijn)).unwrap();
}
