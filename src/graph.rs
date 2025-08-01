use crate::{debruijn::Debruijn, reduce};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeIndex(pub usize);

#[derive(Default, Debug)]
pub struct ReductionGraph {
    pub nodes: Vec<Debruijn>,
    pub unreduced_nodes: Vec<NodeIndex>,
    pub edges: Vec<(NodeIndex, NodeIndex)>,
}

impl ReductionGraph {
    pub fn new() -> ReductionGraph {
        ReductionGraph::default()
    }

    pub fn with_root(root: Debruijn) -> ReductionGraph {
        let mut graph = ReductionGraph::default();
        graph.add_node(root);
        graph
    }

    fn add_node(&mut self, node: Debruijn) -> NodeIndex {
        let index = self.nodes.iter().position(|n| *n == node);
        match index {
            Some(index) => NodeIndex(index),
            None => {
                self.nodes.push(node);
                let index = NodeIndex(self.nodes.len() - 1);
                self.unreduced_nodes.push(index);
                index
            }
        }
    }

    fn add_edge(&mut self, start: NodeIndex, end: NodeIndex) {
        self.edges.push((start, end));
    }

    pub fn reduce_node(&mut self, node_index: NodeIndex) {
        let index = self
            .unreduced_nodes
            .iter()
            .position(|&idx| idx == node_index)
            .unwrap();
        self.unreduced_nodes.remove(index);

        let node = &self.nodes[node_index.0];
        let reductions = reduce::get_reductions(&node);

        for reduced_node in reductions {
            let reduced_node_index = self.add_node(reduced_node);
            self.add_edge(node_index, reduced_node_index);
        }
    }

    pub fn any_reducible(&self) -> bool {
        !self.unreduced_nodes.is_empty()
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::{
        debruijn::Debruijn,
        graph::{NodeIndex, ReductionGraph},
    };

    impl ReductionGraph {
        fn contains_node(&self, node: &Debruijn) -> bool {
            self.nodes.contains(node)
        }

        fn contains_edge(&self, a: &Debruijn, b: &Debruijn) -> bool {
            if let Some(a) = self.get_index(a)
                && let Some(b) = self.get_index(b)
            {
                self.edges.contains(&(a, b))
            } else {
                false
            }
        }

        fn get_index(&self, node: &Debruijn) -> Option<NodeIndex> {
            self.nodes
                .iter()
                .position(|the_node| the_node == node)
                .map(NodeIndex)
        }
    }

    #[test]
    fn graph_and_true_false() {
        let root = "(((λ (λ ((2 1) 2))) (λ (λ 2))) (λ (λ 1)))";
        let root = Debruijn::from_str(root).unwrap();
        let mut graph = ReductionGraph::with_root(root);

        while graph.any_reducible() {
            graph.reduce_node(graph.unreduced_nodes[0]);
        }

        let nodes = [
            "(((λ (λ ((2 1) 2))) (λ (λ 2))) (λ (λ 1)))", // 0
            "((λ (((λ (λ 2)) 1) (λ (λ 2)))) (λ (λ 1)))", // 1
            "(((λ (λ 2)) (λ (λ 1))) (λ (λ 2)))",         // 2
            "((λ ((λ 2) (λ (λ 2)))) (λ (λ 1)))",         // 3
            "((λ (λ (λ 1))) (λ (λ 2)))",                 // 4
            "((λ 1) (λ (λ 1)))",                         // 5
            "(λ (λ 1))",                                 // 6
        ];

        let nodes = nodes.map(|node| Debruijn::from_str(node).unwrap());

        let edges = [
            (0, 1),
            (1, 2),
            (1, 3),
            (2, 4),
            (3, 4),
            (3, 5),
            (4, 6),
            (5, 6),
        ];

        for node in &nodes {
            assert!(graph.contains_node(node))
        }

        for (a, b) in edges {
            let a = &nodes[a];
            let b = &nodes[b];
            assert!(graph.contains_edge(&a, &&b));
        }
    }
}
