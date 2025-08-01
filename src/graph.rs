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
    pub fn new(root: Debruijn) -> ReductionGraph {
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
