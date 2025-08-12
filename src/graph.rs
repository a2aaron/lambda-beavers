use std::{collections::HashMap, fmt::Display};

use crate::{
    debruijn::Debruijn,
    reduce::{self, Fragment},
    replace::{self, TreePath},
};

#[derive(Debug)]
struct Redex {
    func: Debruijn,
    arg: Debruijn,
    treepath: TreePath,
}

impl Redex {
    fn new(func: Debruijn, arg: Debruijn, treepath: TreePath) -> Redex {
        match func {
            Debruijn::Abstraction { .. } => Redex {
                func,
                arg,
                treepath,
            },
            _ => panic!("{func} is not an abstraction!"),
        }
    }

    fn beta_reduce(&self, root: Debruijn) -> RedexResult {
        let fragment = Fragment(reduce::_beta_reduce(&self.func, &self.arg));
        let term = replace::replace(root, fragment.clone(), &self.treepath);
        RedexResult { term }
    }
}

struct RedexResult {
    term: Debruijn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RedexIndex(usize);
impl Display for RedexIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug)]
pub struct ReductionNode {
    pub term: Debruijn,
    redexes: Vec<Redex>,
    pub unevaluated_redexes: Vec<RedexIndex>,
}

impl ReductionNode {
    fn from_term(term: Debruijn) -> ReductionNode {
        let redexes = get_redexes(&term);
        let unevaluated_redexes = (0..redexes.len()).map(|i| RedexIndex(i)).collect();
        ReductionNode {
            term,
            redexes,
            unevaluated_redexes,
        }
    }

    fn get_redex(&self, redex: RedexIndex) -> Option<&Redex> {
        self.redexes.get(redex.0)
    }

    fn evaluate_redex(&mut self, redex_index: RedexIndex) -> RedexResult {
        assert!(self.is_unevaled(redex_index));
        let index = self
            .unevaluated_redexes
            .iter()
            .position(|redex_idx| *redex_idx == redex_index)
            .unwrap();
        self.unevaluated_redexes.remove(index);

        let redex = self.get_redex(redex_index).unwrap();
        redex.beta_reduce(self.term.clone())
    }

    fn is_brnf(&self) -> bool {
        self.redexes.is_empty()
    }

    fn is_unevaled(&self, redex: RedexIndex) -> bool {
        self.unevaluated_redexes.contains(&redex)
    }

    fn has_unevaled_redexes(&self) -> bool {
        !self.unevaluated_redexes.is_empty()
    }
}

fn get_redexes(term: &Debruijn) -> Vec<Redex> {
    fn try_into_redex(term: &Debruijn) -> Option<(Debruijn, Debruijn)> {
        match term {
            Debruijn::Application { func, arg } => match **func {
                Debruijn::Abstraction { .. } => Some((*func.clone(), *arg.clone())),
                _ => None,
            },
            _ => None,
        }
    }
    replace::treepath_filter(term, try_into_redex)
        .into_iter()
        .map(|(treepath, (func, arg))| Redex::new(func, arg, treepath))
        .collect()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeIndex(pub usize);

impl Display for NodeIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Default, Debug)]
pub struct ReductionGraph {
    nodes: Vec<ReductionNode>,
    term_to_node: HashMap<Debruijn, NodeIndex>,
    // TODO: consider moving the reduction strategy stuff to be in graph.rs
    pub incomplete_nodes: Vec<NodeIndex>,
    edges: Vec<(NodeIndex, NodeIndex)>,
    pub beta_reduced_normal_form: Option<NodeIndex>,
    pub root: Option<NodeIndex>,
}

pub struct GraphUpdate {
    pub new_node: Option<NodeIndex>,
    pub new_edge: (NodeIndex, NodeIndex),
    pub is_brnf: bool,
}

impl ReductionGraph {
    pub fn new() -> ReductionGraph {
        ReductionGraph::default()
    }

    pub fn with_root(root: Debruijn) -> ReductionGraph {
        let mut graph = ReductionGraph::default();
        let root = graph.add_node_from_term(root).0;
        graph.root = Some(root);
        graph
    }

    fn add_node_from_term(&mut self, term: Debruijn) -> (NodeIndex, bool) {
        let index = self.term_to_node.get(&term).copied();
        match index {
            Some(index) => (index, false),
            None => {
                let reduction_node = ReductionNode::from_term(term.clone());
                let index = NodeIndex(self.nodes.len());
                self.term_to_node.insert(term, index);
                if reduction_node.has_unevaled_redexes() {
                    self.incomplete_nodes.push(index);
                }
                self.nodes.push(reduction_node);
                (index, true)
            }
        }
    }

    fn add_node_from_redex_result(&mut self, redex_result: RedexResult) -> (NodeIndex, bool) {
        self.add_node_from_term(redex_result.term)
    }

    fn add_edge(&mut self, start: NodeIndex, end: NodeIndex) {
        self.edges.push((start, end));
    }

    pub fn reduce_node(&mut self, node_index: NodeIndex, redex_index: RedexIndex) -> GraphUpdate {
        let node = self.get_mut(node_index).unwrap();
        assert!(
            node.has_unevaled_redexes(),
            "node at {node_index} must have unevaluated redex"
        );

        let redex_result = node.evaluate_redex(redex_index);
        if !node.has_unevaled_redexes() {
            self.set_fully_evaled(node_index);
        }

        let (new_node_index, already_exists) = self.add_node_from_redex_result(redex_result);
        let new_node = self.get(new_node_index).unwrap();

        let is_brnf = new_node.is_brnf();
        if is_brnf {
            assert!(
                self.beta_reduced_normal_form.is_none()
                    || self.beta_reduced_normal_form == Some(new_node_index),
                "BRNF was already found at {} but trying to set it again at {}.",
                self.get(self.beta_reduced_normal_form.unwrap())
                    .unwrap()
                    .term,
                self.get(node_index).unwrap().term,
            );
            self.beta_reduced_normal_form = Some(new_node_index);
        }

        let new_edge = (node_index, new_node_index);
        self.add_edge(node_index, new_node_index);

        GraphUpdate {
            new_node: if already_exists {
                None
            } else {
                Some(new_node_index)
            },
            new_edge,
            is_brnf,
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

    fn get_mut(&mut self, index: NodeIndex) -> Option<&mut ReductionNode> {
        self.nodes.get_mut(index.0)
    }

    pub fn nodes(&self) -> &[ReductionNode] {
        &self.nodes
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
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::{
        debruijn::Debruijn,
        graph::{NodeIndex, ReductionGraph, ReductionNode},
    };

    impl ReductionGraph {
        fn contains_term(&self, term: &Debruijn) -> bool {
            self.get_by_term(term).is_some()
        }

        fn contains_edge(&self, a: &Debruijn, b: &Debruijn) -> bool {
            if let Some(a) = self.get_by_term(a)
                && let Some(b) = self.get_by_term(b)
            {
                self.edges.contains(&(a, b))
            } else {
                false
            }
        }

        fn get_by_term(&self, node: &Debruijn) -> Option<NodeIndex> {
            self.nodes
                .iter()
                .position(|the_node| the_node.term == *node)
                .map(NodeIndex)
        }
    }

    #[test]
    fn brnf_check() {
        let term = "(λ 1) λ λ 1";
        let term = Debruijn::from_str(term).unwrap();
        let node = ReductionNode::from_term(term);
        assert!(
            !node.is_brnf(),
            "Expected {} to be BRNF. Redex: {:?}",
            node.term,
            node.redexes
        );
    }

    #[test]
    fn graph_and_true_false() {
        let root = "(((λ (λ ((2 1) 2))) (λ (λ 2))) (λ (λ 1)))";
        let root = Debruijn::from_str(root).unwrap();
        let mut graph = ReductionGraph::with_root(root);

        while graph.any_reducible() {
            let node_idx = graph.incomplete_nodes[0];
            let node = graph.get(node_idx).unwrap();
            let redex = node.unevaluated_redexes[0];
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
            assert!(graph.contains_term(node))
        }

        for (a, b) in edges {
            let a = &nodes[a];
            let b = &nodes[b];
            assert!(graph.contains_edge(&a, &&b));
        }
    }
}
