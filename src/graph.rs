use crate::{debruijn::Debruijn, reduce};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeIndex(pub usize);

#[derive(Default, Debug)]
pub struct ReductionGraph {
    pub nodes: Vec<Debruijn>,
    pub unreduced_nodes: Vec<NodeIndex>,
    pub edges: Vec<(NodeIndex, NodeIndex)>,
    pub beta_reduced_normal_form: Option<NodeIndex>,
    pub root: Option<NodeIndex>,
}

pub struct GraphUpdate {
    pub new_nodes: Vec<NodeIndex>,
    pub new_edges: Vec<(NodeIndex, NodeIndex)>,
    pub is_brnf: bool,
}

impl ReductionGraph {
    pub fn new() -> ReductionGraph {
        ReductionGraph::default()
    }

    pub fn with_root(root: Debruijn) -> ReductionGraph {
        let mut graph = ReductionGraph::default();
        let root = graph.add_node(root).0;
        graph.root = Some(root);
        graph
    }

    fn add_node(&mut self, node: Debruijn) -> (NodeIndex, bool) {
        let index = self.nodes.iter().position(|n| *n == node);
        match index {
            Some(index) => (NodeIndex(index), false),
            None => {
                self.nodes.push(node);
                let index = NodeIndex(self.nodes.len() - 1);
                self.unreduced_nodes.push(index);
                (index, true)
            }
        }
    }

    fn add_edge(&mut self, start: NodeIndex, end: NodeIndex) {
        self.edges.push((start, end));
    }

    pub fn reduce_node(&mut self, node_index: NodeIndex) -> GraphUpdate {
        let index = self
            .unreduced_nodes
            .iter()
            .position(|&idx| idx == node_index)
            .unwrap();
        self.unreduced_nodes.remove(index);

        let node = &self.nodes[node_index.0];
        let reductions = reduce::get_reductions(&node);

        let is_brnf = reductions.len() == 0;

        if is_brnf {
            assert!(
                self.beta_reduced_normal_form.is_none()
                    || self.beta_reduced_normal_form == Some(node_index)
            );

            self.beta_reduced_normal_form = Some(node_index);
        }

        let reductions: Vec<(NodeIndex, bool)> = reductions
            .into_iter()
            .map(|node| self.add_node(node))
            .collect();
        let new_edges: Vec<(NodeIndex, NodeIndex)> = reductions
            .iter()
            .map(|(new_node, _already_added)| (node_index, *new_node))
            .collect();

        for (existing_node, new_node) in &new_edges {
            self.add_edge(*existing_node, *new_node);
        }

        // nodes not already in the tree (note: this means new_edges may contain edges not in new_nodes due to
        // the end node being in the tree already)
        let new_nodes: Vec<NodeIndex> = reductions
            .iter()
            .filter_map(|(node_index, already_added)| {
                if *already_added {
                    None
                } else {
                    Some(*node_index)
                }
            })
            .collect();
        return GraphUpdate {
            new_nodes,
            new_edges,
            is_brnf,
        };
    }

    pub fn any_reducible(&self) -> bool {
        !self.unreduced_nodes.is_empty()
    }

    pub fn get(&self, node: NodeIndex) -> Option<Debruijn> {
        self.nodes.get(node.0).cloned()
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
