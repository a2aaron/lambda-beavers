use std::{fmt::Display, ops::ControlFlow};

use clap::ValueEnum;

use crate::{
    debruijn::Debruijn,
    debruijn_flat::{self, FlatRoot},
    graph::{NodeIndex, ReductionGraph},
    treewalk::VisitOrder,
    utils::Rng,
};

pub struct Reducer {
    pub root: FlatRoot,
    visit_order: VisitOrder,
}

impl Reducer {
    pub fn new(root: &Debruijn, visit_order: VisitOrder) -> Self {
        Self {
            root: FlatRoot::from(root),
            visit_order,
        }
    }

    pub fn reduce_one(&mut self) -> Option<ReductionResult> {
        let result =
            self.visit_order
                .preorder_walk_mut(&mut self.root, |root, term, parent_chain| {
                    if let Some(redex) =
                        debruijn_flat::RedexMut::try_get(root, term, parent_chain.clone())
                    {
                        debruijn_flat::beta_reduce(root, redex);
                        ControlFlow::Break(())
                    } else {
                        ControlFlow::Continue(())
                    }
                });
        match result {
            Some(()) => None,
            // This clone is fine, it occurs at the end of all reductions
            None => Some(ReductionResult::NormalForm(Debruijn::from(&self.root))),
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

pub fn reduce(
    root: &Debruijn,
    visit_order: VisitOrder,
    max_reductions: usize,
) -> (ReductionResult, usize) {
    let mut reducer = Reducer::new(root, visit_order);
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

    use crate::{debruijn::Debruijn, reduce::Reducer, treewalk::VisitOrder};

    fn assert_usage(reducer: &Reducer) {
        if let Err((failing_term, actual, expected)) = reducer.root.check_usage() {
            panic!(
                "Expected usage to be {expected} but got {actual} for node {failing_term} in {}",
                reducer.root
            );
        }
    }

    #[test]
    fn parent_usage_simplest() {
        let root = Debruijn::from_str("λ (λ 1 1) (1 1)").unwrap();
        let mut reducer = Reducer::new(&root, VisitOrder::LEFT_OUTERMOST);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn parent_usage_open_terms() {
        let root = Debruijn::from_str("λ (λ 1 1) 99").unwrap();
        let mut reducer = Reducer::new(&root, VisitOrder::LEFT_OUTERMOST);
        reducer.reduce_one();
        assert_usage(&reducer);
    }

    #[test]
    fn parent_usage() {
        let root =
            Debruijn::from_str("(λ λ λ 3 1 (2 1)) ((λ λ 2) (λ λ λ 3 1 (2 1))) λ λ 2").unwrap();
        let mut reducer = Reducer::new(&root, VisitOrder::LEFT_OUTERMOST);

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
