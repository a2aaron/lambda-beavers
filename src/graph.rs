use std::{collections::HashMap, fmt::Display};

use crate::debruijn_flat::{FlatTree, RedexMut, beta_reduce};

#[derive(Debug)]
pub struct ReductionNode {
    pub tree: FlatTree,
    pub unevaluated_redexes: Vec<RedexMut>,
}

impl ReductionNode {
    fn from_root(tree: FlatTree) -> ReductionNode {
        let unevaluated_redexes = tree.get_redexes();
        ReductionNode {
            tree,
            unevaluated_redexes,
        }
    }

    fn evaluate_redex(&mut self, redex: RedexMut) -> FlatTree {
        let redex_index = self.unevaluated_redexes.iter().position(|r| *r == redex);
        assert!(redex_index.is_some());
        self.unevaluated_redexes.remove(redex_index.unwrap());

        let mut tree = self.tree.clone();
        beta_reduce(&mut tree, &redex);
        tree.normalized()
    }

    fn has_unevaled_redexes(&self) -> bool {
        !self.unevaluated_redexes.is_empty()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeIndex(usize);

impl Display for NodeIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "node_{}", self.0)
    }
}

#[derive(Debug)]
pub struct ReductionGraph {
    nodes: Vec<ReductionNode>,
    term_to_node: HashMap<FlatTree, NodeIndex>,
    pub incomplete_nodes: Vec<NodeIndex>,
    edges: Vec<(NodeIndex, NodeIndex)>,
    beta_normal_form: Option<NodeIndex>,
    root: Option<NodeIndex>,
}

pub struct GraphUpdate {
    pub new_node: Option<NodeIndex>,
    pub new_edge: (NodeIndex, NodeIndex),
    pub is_bnf: bool,
}

impl ReductionGraph {
    fn new() -> ReductionGraph {
        ReductionGraph {
            nodes: vec![],
            term_to_node: HashMap::new(),
            incomplete_nodes: vec![],
            edges: vec![],
            beta_normal_form: None,
            root: None,
        }
    }

    pub fn with_tree(tree: FlatTree) -> ReductionGraph {
        let mut graph = ReductionGraph::new();
        let root_index = graph.add_node_from_tree(tree).0;
        graph.root = Some(root_index);
        graph
    }

    fn add_node_from_tree(&mut self, tree: FlatTree) -> (NodeIndex, bool) {
        let index = self.term_to_node.get(&tree).copied();
        match index {
            Some(index) => (index, false),
            None => {
                // Rc clone is cheap
                let reduction_node = ReductionNode::from_root(tree.clone());
                let index = NodeIndex(self.nodes.len());
                self.term_to_node.insert(tree, index);
                if reduction_node.has_unevaled_redexes() {
                    self.incomplete_nodes.push(index);
                }

                if reduction_node.tree.is_bnf() {
                    assert!(
                        self.beta_normal_form.is_none(),
                        "BNF was already found at {:#?} but trying to set it again at {:#?}.",
                        self.bnf().unwrap(),
                        reduction_node
                    );
                    self.beta_normal_form = Some(index);
                }

                self.nodes.push(reduction_node);
                (index, true)
            }
        }
    }

    fn add_edge(&mut self, start: NodeIndex, end: NodeIndex) {
        self.edges.push((start, end));
    }

    pub fn reduce_node(&mut self, node_index: NodeIndex, redex: RedexMut) -> GraphUpdate {
        let node = self.nodes.get_mut(node_index.0).unwrap();
        assert!(
            node.has_unevaled_redexes(),
            "node at {node_index} must have unevaluated redex"
        );

        let reduced_term = node.evaluate_redex(redex);
        if !node.has_unevaled_redexes() {
            self.set_fully_evaled(node_index);
        }

        let (new_node_index, already_exists) = self.add_node_from_tree(reduced_term);
        let new_node = self.get(new_node_index).unwrap();
        let is_bnf = new_node.tree.is_bnf();

        let new_edge = (node_index, new_node_index);
        self.add_edge(node_index, new_node_index);

        GraphUpdate {
            new_node: if already_exists {
                None
            } else {
                Some(new_node_index)
            },
            new_edge,
            is_bnf,
        }
    }

    fn set_fully_evaled(&mut self, node_index: NodeIndex) {
        assert!(!self.get(node_index).unwrap().has_unevaled_redexes());
        let index = self
            .incomplete_nodes
            .iter()
            .position(|idx| *idx == node_index)
            .unwrap();
        self.incomplete_nodes.remove(index);
    }

    pub fn any_reducible(&self) -> bool {
        !self.incomplete_nodes.is_empty()
    }

    pub fn get(&self, index: NodeIndex) -> Option<&ReductionNode> {
        self.nodes.get(index.0)
    }

    pub fn nodes(&self) -> impl Iterator<Item = (&ReductionNode, NodeIndex)> {
        self.nodes
            .iter()
            .enumerate()
            .map(|(i, node)| (node, NodeIndex(i)))
    }

    pub fn edges(&self) -> &[(NodeIndex, NodeIndex)] {
        &self.edges
    }

    pub fn incomplete_nodes(&self) -> &[NodeIndex] {
        &self.incomplete_nodes
    }

    pub fn num_unevaluated_redexes(&self) -> usize {
        self.nodes
            .iter()
            .map(|node| node.unevaluated_redexes.len())
            .sum()
    }

    pub fn root(&self) -> Option<(&ReductionNode, NodeIndex)> {
        match self.root {
            Some(root) => Some((self.get(root).unwrap(), root)),
            None => None,
        }
    }

    pub fn bnf(&self) -> Option<(&ReductionNode, NodeIndex)> {
        match self.beta_normal_form {
            Some(bnf) => Some((self.get(bnf).unwrap(), bnf)),
            None => None,
        }
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::{
        debruijn_flat::FlatTree,
        graph::{NodeIndex, ReductionGraph, ReductionNode},
    };

    impl ReductionGraph {
        fn contains_term(&self, term: &FlatTree) -> bool {
            self.get_by_term(term).is_some()
        }

        fn contains_edge(&self, a: &FlatTree, b: &FlatTree) -> bool {
            if let Some(a) = self.get_by_term(a)
                && let Some(b) = self.get_by_term(b)
            {
                self.edges.contains(&(a, b))
            } else {
                false
            }
        }

        fn get_by_term(&self, tree: &FlatTree) -> Option<NodeIndex> {
            // Note: Normalized is used here since the graph has no control over the inner layout
            // of a given node.
            self.nodes
                .iter()
                .position(|the_node| the_node.tree.normalized() == tree.normalized())
                .map(NodeIndex)
        }
    }

    #[test]
    fn bnf_check() {
        let term = "(λ 1) λ λ 1";
        let tree = FlatTree::from_str(term).unwrap();
        let node = ReductionNode::from_root(tree.clone());
        assert!(
            !node.tree.is_bnf(),
            "Expected {} to be BNF. Redex: {:?}",
            node.tree,
            tree.get_redexes()
        );
    }

    #[test]
    fn graph_and_true_false() {
        let term = "(((λ (λ ((2 1) 2))) (λ (λ 2))) (λ (λ 1)))";
        let tree = FlatTree::from_str(term).unwrap().into();
        let mut graph = ReductionGraph::with_tree(tree);

        while graph.any_reducible() {
            let node_idx = graph.incomplete_nodes[0];
            let node = graph.get(node_idx).unwrap();
            let redex = node.unevaluated_redexes[0].clone();
            graph.reduce_node(node_idx, redex);
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

        let nodes = nodes.map(|node| FlatTree::from_str(node).unwrap());

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

        for node in &graph.nodes {
            println!("node: {}", node.tree);
        }

        for node in &nodes {
            assert!(
                graph.contains_term(node),
                "Expected graph to contain node {} but it didn't",
                node
            )
        }

        for (a, b) in edges {
            let a = &nodes[a];
            let b = &nodes[b];
            assert!(graph.contains_edge(&a, &&b));
        }
    }
}
