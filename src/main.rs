#![feature(iter_intersperse)]
#![feature(hash_set_entry)]
#![feature(macro_metavar_expr_concat)]
#![feature(type_alias_impl_trait)]
#![feature(never_type)]

use lambda_beaver::{
    debruijn::Debruijn,
    graph::ReductionGraph,
    parse_binary,
    reduce::ReductionStrategy,
    utils::{self},
};

fn reduce(
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

#[allow(unused_variables)]
fn main() {
    for length in 0..16 {
        let terms = utils::bitstring_permutations(length)
            .filter_map(|bitstring| parse_binary::from_vec(bitstring.to_vec()).ok());

        for term in terms {
            let mut graph = ReductionGraph::with_root(term.clone());
            let brnf = reduce(&mut graph, ReductionStrategy::DFS, 10_000);
            if let Some((brnf, reductions_used)) = brnf {
                let binary_term = format!("{:b}", term);
                let binary_brnf = format!("{:b}", brnf);
                println!(
                    "{} -> {} | {} -> {} | lengths: {} -> {} | found in {}",
                    binary_term,
                    binary_brnf,
                    term,
                    brnf,
                    binary_term.len(),
                    binary_brnf.len(),
                    reductions_used
                );
            } else {
                println!(
                    "{:b} [{}] -> <not found after 10000 reductions>",
                    term, term
                );
            }
        }
    }
}
