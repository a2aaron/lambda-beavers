use std::{collections::HashMap, fmt::Display, rc::Rc};

use crate::{
    debruijn::Debruijn,
    reduce::{self, Fragment},
    replace::{self, TreePath, VisitOrder},
};

#[derive(Debug, Clone)]
pub struct Redex {
    pub redex: Rc<Debruijn>,
    pub treepath: TreePath,
}

impl Redex {
    fn new(redex: Rc<Debruijn>, treepath: TreePath) -> Redex {
        if !is_redex(&redex) {
            panic!("{redex} is not a redex!");
        }
        Redex { redex, treepath }
    }

    pub fn beta_reduce(&self, root: &Debruijn) -> Debruijn {
        let fragment = Fragment(&reduce::beta_reduce(&self.redex));
        let term = replace::replace(root, fragment, &self.treepath);
        term
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RedexIndex(usize);
impl Display for RedexIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "redex_{}", self.0)
    }
}

#[derive(Debug)]
pub struct ReductionNode {
    pub term: Rc<Debruijn>,
    redexes: Vec<Redex>,
    pub unevaluated_redexes: Vec<RedexIndex>,
}

impl ReductionNode {
    fn from_term(term: Rc<Debruijn>, visit_order: VisitOrder) -> ReductionNode {
        let redexes = get_redexes(&term, visit_order);
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

    fn evaluate_redex(&mut self, redex_index: RedexIndex) -> Debruijn {
        assert!(self.is_unevaled(redex_index));
        let index = self
            .unevaluated_redexes
            .iter()
            .position(|redex_idx| *redex_idx == redex_index)
            .unwrap();
        self.unevaluated_redexes.remove(index);

        let redex = self.get_redex(redex_index).unwrap();
        redex.beta_reduce(&self.term)
    }

    fn is_bnf(&self) -> bool {
        self.redexes.is_empty()
    }

    fn is_unevaled(&self, redex: RedexIndex) -> bool {
        self.unevaluated_redexes.contains(&redex)
    }

    fn has_unevaled_redexes(&self) -> bool {
        !self.unevaluated_redexes.is_empty()
    }
}

fn is_redex(term: &Debruijn) -> bool {
    if let Debruijn::Application { func, .. } = term
        && let Debruijn::Abstraction { .. } = &**func
    {
        return true;
    }
    false
}

pub fn get_redexes(term: &Rc<Debruijn>, visit_order: VisitOrder) -> Vec<Redex> {
    fn try_into_redex(term: &Rc<Debruijn>, treepath: TreePath) -> Option<Redex> {
        if is_redex(&term) {
            Some(Redex::new(term.clone(), treepath))
        } else {
            None
        }
    }
    replace::treepath_filter::<Redex>(&term, try_into_redex, visit_order)
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
    term_to_node: HashMap<Rc<Debruijn>, NodeIndex>,
    // TODO: consider moving the reduction strategy stuff to be in graph.rs
    pub incomplete_nodes: Vec<NodeIndex>,
    edges: Vec<(NodeIndex, NodeIndex)>,
    beta_normal_form: Option<NodeIndex>,
    root: Option<NodeIndex>,
    visit_order: VisitOrder,
}

pub struct GraphUpdate {
    pub new_node: Option<NodeIndex>,
    pub new_edge: (NodeIndex, NodeIndex),
    pub is_bnf: bool,
}

impl ReductionGraph {
    fn new(visit_order: VisitOrder) -> ReductionGraph {
        ReductionGraph {
            nodes: vec![],
            term_to_node: HashMap::new(),
            incomplete_nodes: vec![],
            edges: vec![],
            beta_normal_form: None,
            root: None,
            visit_order,
        }
    }

    pub fn with_root(root: Debruijn, visit_order: VisitOrder) -> ReductionGraph {
        let root = Rc::new(root);
        let mut graph = ReductionGraph::new(visit_order);
        let root = graph.add_node_from_term(root).0;
        graph.root = Some(root);
        graph
    }

    fn add_node_from_term(&mut self, term: Rc<Debruijn>) -> (NodeIndex, bool) {
        let index = self.term_to_node.get(&term).copied();
        match index {
            Some(index) => (index, false),
            None => {
                // Rc clone is cheap
                let reduction_node = ReductionNode::from_term(term.clone(), self.visit_order);
                let index = NodeIndex(self.nodes.len());
                self.term_to_node.insert(term, index);
                if reduction_node.has_unevaled_redexes() {
                    self.incomplete_nodes.push(index);
                }

                if reduction_node.is_bnf() {
                    assert!(
                        self.beta_normal_form.is_none(),
                        "BNF was already found at {} but trying to set it again at {}.",
                        self.get(self.beta_normal_form.unwrap()).unwrap().term,
                        reduction_node.term
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

    pub fn reduce_node(&mut self, node_index: NodeIndex, redex_index: RedexIndex) -> GraphUpdate {
        let node = self.get_mut(node_index).unwrap();
        assert!(
            node.has_unevaled_redexes(),
            "node at {node_index} must have unevaluated redex"
        );

        let reduced_term = Rc::new(node.evaluate_redex(redex_index));
        if !node.has_unevaled_redexes() {
            self.set_fully_evaled(node_index);
        }

        let (new_node_index, already_exists) = self.add_node_from_term(reduced_term);
        let new_node = self.get(new_node_index).unwrap();
        let is_bnf = new_node.is_bnf();

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

    fn get_mut(&mut self, index: NodeIndex) -> Option<&mut ReductionNode> {
        self.nodes.get_mut(index.0)
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
    use std::{rc::Rc, str::FromStr};

    use crate::{
        debruijn::Debruijn,
        graph::{NodeIndex, ReductionGraph, ReductionNode},
        replace::VisitOrder,
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
                .position(|the_node| the_node.term.as_ref() == node)
                .map(NodeIndex)
        }
    }

    #[test]
    fn bnf_check() {
        let term = "(λ 1) λ λ 1";
        let term = Rc::new(Debruijn::from_str(term).unwrap());
        let node = ReductionNode::from_term(term, VisitOrder::LEFT_INNERMOST);
        assert!(
            !node.is_bnf(),
            "Expected {} to be BNF. Redex: {:?}",
            node.term,
            node.redexes
        );
    }

    #[test]
    fn graph_and_true_false() {
        let root = "(((λ (λ ((2 1) 2))) (λ (λ 2))) (λ (λ 1)))";
        let root = Debruijn::from_str(root).unwrap();
        let mut graph = ReductionGraph::with_root(root, VisitOrder::LEFT_INNERMOST);

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
