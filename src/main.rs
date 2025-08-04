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

enum ReductionResult {
    NormalForm(Debruijn),
    Irreducible,
    MaxReductionsReached,
}

fn reduce(
    graph: &mut ReductionGraph,
    reduction_strategy: ReductionStrategy,
    max: usize,
) -> (ReductionResult, usize) {
    for i in 0..max {
        let node_to_reduce = reduction_strategy.get_node(graph);
        match node_to_reduce {
            Some(node_to_reduce) => {
                let graph_update = graph.reduce_node(node_to_reduce);
                if graph_update.is_brnf {
                    let reduced_term = graph.get(node_to_reduce).unwrap();
                    return (ReductionResult::NormalForm(reduced_term), i);
                }
            }
            _ => return (ReductionResult::Irreducible, i),
        }
    }
    (ReductionResult::MaxReductionsReached, max)
}

#[allow(unused_variables)]
fn main() {
    let max = 10_0;

    for length in 0..=22 {
        let terms = utils::bitstring_permutations(length)
            .filter_map(|bitstring| parse_binary::from_vec(bitstring.to_vec()).ok());

        for term in terms {
            let mut graph = ReductionGraph::with_root(term.clone());
            let (result, reductions_used) = reduce(&mut graph, ReductionStrategy::DFS, max);
            match result {
                ReductionResult::NormalForm(brnf) => {
                    let binary_term = format!("{:b}", term);
                    let binary_brnf = format!("{:b}", brnf);
                    println!(
                        "{binary_term} -> {binary_brnf} | {term} -> {brnf} | lengths: {} -> {} | found in {reductions_used}",
                        binary_term.len(),
                        binary_brnf.len(),
                    );
                }
                ReductionResult::Irreducible => println!(
                    "{term:b} [{term}] -> <proved irreducible after {reductions_used} reductions>"
                ),
                ReductionResult::MaxReductionsReached => {
                    println!("{term:b} [{term}] -> <not found after {reductions_used} reductions>")
                }
            }
        }
    }
}
