use std::{fmt::Display, ops::ControlFlow};

use clap::ValueEnum;

use crate::{
    debruijn::Debruijn,
    debruijn_flat::{self, FlatTree},
    graph::{NodeIndex, ReductionGraph},
    utils::Rng,
};

pub struct Reducer {
    pub tree: FlatTree,
}

impl Reducer {
    pub fn new(term: &Debruijn) -> Self {
        Self {
            tree: FlatTree::from(term),
        }
    }

    pub fn reduce_one(&mut self) -> Option<ReductionResult> {
        let result = self.tree.preorder_walk_mut(|tree, ctx| {
            if let Some(redex) = debruijn_flat::RedexMut::try_get(tree, ctx) {
                debruijn_flat::beta_reduce(tree, redex);
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        });
        match result {
            Some(()) => None,
            // This clone is fine, it occurs at the end of all reductions
            None => Some(ReductionResult::NormalForm(Debruijn::from(&self.tree))),
        }
    }
}

pub enum ReductionResult {
    NormalForm(Debruijn),
    Irreducible,
    MaxReductionsReached,
}

impl Display for ReductionResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReductionResult::NormalForm(term) => write!(f, "Normal Form: {}", term),
            ReductionResult::Irreducible => write!(f, "Irreducible"),
            ReductionResult::MaxReductionsReached => write!(f, "Max Reductions Reached"),
        }
    }
}

pub fn reduce(term: &Debruijn, max_reductions: usize) -> (ReductionResult, usize) {
    let mut reducer = Reducer::new(term);
    for i in 0..max_reductions {
        if let Some(value) = reducer.reduce_one() {
            return (value, i);
        }
    }
    (ReductionResult::MaxReductionsReached, max_reductions)
}

pub enum ReductionStrategy {
    DFS,
    BFS,
    Random(Rng),
}

impl ReductionStrategy {
    pub fn get_node(&mut self, graph: &mut ReductionGraph) -> Option<NodeIndex> {
        if !graph.any_reducible() {
            return None;
        }
        let node = match self {
            ReductionStrategy::DFS => graph.incomplete_nodes[graph.incomplete_nodes.len() - 1],
            ReductionStrategy::BFS => graph.incomplete_nodes[0],
            ReductionStrategy::Random(rng) => {
                let index = rng.rand_usize() % graph.incomplete_nodes.len();
                graph.incomplete_nodes[index]
            }
        };
        Some(node)
    }

    pub fn random() -> ReductionStrategy {
        ReductionStrategy::Random(Rng::new())
    }
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum ReductionStrategyKind {
    DFS,
    BFS,
    Random,
}

impl From<ReductionStrategyKind> for ReductionStrategy {
    fn from(value: ReductionStrategyKind) -> Self {
        match value {
            ReductionStrategyKind::DFS => ReductionStrategy::DFS,
            ReductionStrategyKind::BFS => ReductionStrategy::BFS,
            ReductionStrategyKind::Random => ReductionStrategy::random(),
        }
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::{debruijn::Debruijn, reduce::Reducer};

    #[track_caller]
    fn assert_usage(reducer: &Reducer) {
        if let Err((failing_term, actual, expected)) = reducer.tree.check_usage() {
            panic!(
                "Expected usage to be {expected} but got {actual} for node {failing_term} in {}",
                reducer.tree
            );
        }
    }

    #[test]
    fn parent_usage_simplest() {
        let term = Debruijn::from_str("λ (λ 1 1) (1 1)").unwrap();
        let mut reducer = Reducer::new(&term);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn parent_usage_open_terms() {
        let term = Debruijn::from_str("λ (λ 1 1) 99").unwrap();
        let mut reducer = Reducer::new(&term);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn parent_usage() {
        let term =
            Debruijn::from_str("(λ λ λ 3 1 (2 1)) ((λ λ 2) (λ λ λ 3 1 (2 1))) λ λ 2").unwrap();
        let mut reducer = Reducer::new(&term);

        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn parent_usage_another() {
        let term = Debruijn::from_str("(λ λ 3 2) (λ λ 2)").unwrap();
        let mut reducer = Reducer::new(&term);

        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn parent_usage2() {
        let term = Debruijn::from_str("(λ λ 1) 10").unwrap();
        let mut reducer = Reducer::new(&term);

        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn usage3() {
        let term = Debruijn::from_str("λ λ λ λ (λ λ 6) 2 1").unwrap();
        let mut reducer = Reducer::new(&term);

        reducer.reduce_one();
        println!("{}", reducer.tree);
        reducer.reduce_one();
        println!("{}", reducer.tree);
        assert_usage(&reducer);
    }

    #[test]
    fn usage4() {
        let term = Debruijn::from_str("λ ((λ λ 1) 99) 1 99").unwrap();
        let mut reducer = Reducer::new(&term);

        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn usage4_simpler() {
        let term = Debruijn::from_str("λ ((λ λ 1) 99) 1").unwrap();
        let mut reducer = Reducer::new(&term);

        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn parent_usage_simpler() {
        let term = Debruijn::from_str("λ (λ λ λ 2) 100").unwrap();
        let mut reducer = Reducer::new(&term);

        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn from_fuzzer() {
        let term = "λ (λ 1 λ 1) λ λ 3";
        let term = Debruijn::from_str(term).unwrap();
        let mut reducer = Reducer::new(&term);

        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn from_fuzzer2() {
        let term = "(λ 1 λ 3) λ 1";
        let term = Debruijn::from_str(term).unwrap();
        let mut reducer = Reducer::new(&term);

        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn from_fuzzer3() {
        let term = "(λ λ 2 1) λ 1";
        let term = Debruijn::from_str(term).unwrap();
        let mut reducer = Reducer::new(&term);

        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn parent_usage_simple_2() {
        let term = Debruijn::from_str("λ (λ λ 1) 100").unwrap();
        let mut reducer = Reducer::new(&term);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn fuzzer4() {
        let term = Debruijn::from_str("2 1 λ λ (λ λ 1 20 2) 20 λ 2 λ λ λ 22 λ λ λ λ λ λ λ λ λ 22 λ 5 λ λ λ 5 λ λ (λ λ 1 20 2) 20 λ 2 λ 1 22").unwrap();
        let mut reducer = Reducer::new(&term);
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn fuzzer5() {
        let term = Debruijn::from_str(
            "λ λ λ (7 13) λ λ λ λ λ λ λ λ λ λ λ λ λ λ λ (λ λ λ λ λ λ λ λ λ λ λ λ λ 13 13) λ λ λ λ λ λ λ λ λ λ λ λ λ λ λ λ (λ λ λ λ λ λ λ λ λ λ λ λ λ λ λ 15 λ 15) 15 λ λ λ λ λ λ λ λ 255",
        ).unwrap();
        let mut reducer = Reducer::new(&term);

        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn fuzzer6() {
        let testcase = "(λ λ 1) 99 λ (λ λ 1 3) 99 99";
        let term = Debruijn::from_str(testcase).unwrap();
        let mut reducer = Reducer::new(&term);

        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn fuzzer7() {
        let testcase = "(λ 1 1) (λ 1) 11";
        let term = Debruijn::from_str(testcase).unwrap();
        let mut reducer = Reducer::new(&term);

        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
        reducer.reduce_one();
        assert_usage(&reducer);
    }
}
