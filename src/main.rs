#![feature(iter_intersperse)]
#![feature(hash_set_entry)]
#![feature(macro_metavar_expr_concat)]
#![feature(type_alias_impl_trait)]
#![feature(never_type)]

use std::collections::HashMap;

use lambda_beaver::{
    debruijn::Debruijn,
    graph::ReductionGraph,
    parse_binary,
    reduce::ReductionStrategy,
    term::Term,
    utils::{self},
};

enum ReductionResult {
    NormalForm(Debruijn),
    Irreducible,
    MaxReductionsReached,
}

fn reduce(
    graph: &mut ReductionGraph,
    reduction_strategy: &mut ReductionStrategy,
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

struct Histogram(HashMap<String, usize>);
impl Histogram {
    fn new() -> Histogram {
        Histogram(HashMap::new())
    }

    fn add_irreducable(&mut self) {
        *self.0.entry("IR".to_string()).or_insert(0) += 1;
    }

    fn add_timeout(&mut self) {
        *self.0.entry("TO".to_string()).or_insert(0) += 1;
    }

    fn add(&mut self, value: usize) {
        *self.0.entry(format!("{value:02}")).or_insert(0) += 1;
    }

    fn print(&self) {
        let mut keys: Vec<String> = self.0.keys().cloned().collect();
        keys.sort();
        for key in keys {
            let value = self.0[&key];
            println!("{key}: {value}");
        }
    }
}

#[allow(unused_variables)]
fn main() {
    let mut reduction_strategy = ReductionStrategy::random();
    let max = 1_000;
    let mut histogram_lengths = Histogram::new();
    let mut histogram_time = Histogram::new();

    for length in 0..=25 {
        let terms = utils::bitstring_permutations(length)
            .filter_map(|bitstring| parse_binary::from_vec(bitstring.to_vec()).ok());

        for term in terms {
            let mut graph = ReductionGraph::with_root(term.clone());
            let (result, reductions_used) = reduce(&mut graph, &mut reduction_strategy, max);
            match result {
                ReductionResult::NormalForm(brnf) => {
                    let binary_term = format!("{:b}", term);
                    let binary_brnf = format!("{:b}", brnf);
                    println!(
                        "{binary_term} -> {binary_brnf} | {term} -> {brnf} | lengths: {} -> {} | found in {reductions_used}",
                        binary_term.len(),
                        binary_brnf.len(),
                    );
                    histogram_lengths.add(binary_brnf.len());
                    histogram_time.add(reductions_used);
                }
                ReductionResult::Irreducible => {
                    let term_classic = Term::from(&term);
                    println!(
                        "{term:b} [{term}] [{term_classic}] -> <proved irreducible after {reductions_used} reductions>"
                    );
                    histogram_lengths.add_irreducable();
                    histogram_time.add_irreducable();
                }
                ReductionResult::MaxReductionsReached => {
                    let term_classic = Term::from(&term);
                    println!(
                        "{term:b} [{term}] [{term_classic}] -> <not found after {reductions_used} reductions>"
                    );
                    histogram_lengths.add_timeout();
                    histogram_time.add_timeout();
                }
            }
        }
    }
    println!("Histogram - Lengths");
    histogram_lengths.print();
    println!("Histogram - Time");
    histogram_time.print();
}
