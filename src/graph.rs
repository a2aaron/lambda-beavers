use std::fmt::Display;

use crate::{
    debruijn::{call, def, idx, Debruijn},
    reduce,
};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum Direction {
    Left,
    Right,
}

impl Display for Direction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Direction::Left => write!(f, "L"),
            Direction::Right => write!(f, "R"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TreePath(Vec<Direction>);

impl Display for TreePath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            write!(f, "<root>")
        } else {
            write!(
                f,
                "{}",
                self.0
                    .iter()
                    .map(|x| x.to_string())
                    .intersperse(" ".to_string())
                    .collect::<String>()
            )
        }
    }
}

fn treepath_filter<T>(
    term: &Debruijn,
    filter_map: fn(&Debruijn) -> Option<T>,
) -> Vec<(TreePath, T)> {
    fn _treepath_filter<T>(
        term: &Debruijn,
        filter_map: fn(&Debruijn) -> Option<T>,
        current_path: &mut TreePath,
        emits: &mut Vec<(TreePath, T)>,
    ) {
        if let Some(value) = filter_map(term) {
            emits.push((current_path.clone(), value));
        }

        match term {
            Debruijn::Index(_) => (),
            Debruijn::Application { func, arg } => {
                current_path.0.push(Direction::Left);
                _treepath_filter(&func, filter_map, current_path, emits);
                current_path.0.pop();

                current_path.0.push(Direction::Right);
                _treepath_filter(&arg, filter_map, current_path, emits);
                current_path.0.pop();
            }
            Debruijn::Abstraction { body } => {
                _treepath_filter(body, filter_map, current_path, emits)
            }
        }
    }

    let mut current_path = TreePath(vec![]);
    let mut emits = vec![];
    _treepath_filter(term, filter_map, &mut current_path, &mut emits);
    emits
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Fragment(Debruijn);

impl Display for Fragment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

fn beta_reduce_if_possible(term: &Debruijn) -> Option<Fragment> {
    match term {
        Debruijn::Application { func, arg } => match &**func {
            Debruijn::Abstraction { body } => Some(Fragment(reduce::__beta_reduce(body, arg))),
            _ => None,
        },
        _ => None,
    }
}

fn get<'a>(root: &'a Debruijn, treepath: &TreePath) -> Option<&'a Debruijn> {
    fn _get<'a>(root: &'a Debruijn, treepath: &TreePath, i: usize) -> Option<&'a Debruijn> {
        match root {
            Debruijn::Index(_) => None,
            Debruijn::Application {
                func: left,
                arg: right,
            } => match treepath.0.get(i) {
                Some(direction) => {
                    if *direction == Direction::Left {
                        _get(left, treepath, i + 1)
                    } else {
                        _get(right, treepath, i + 1)
                    }
                }
                None => Some(root),
            },
            Debruijn::Abstraction { body } => _get(body, treepath, i),
        }
    }
    _get(root, treepath, 0)
}

fn replace(root: Debruijn, replacement: Fragment, treepath: &TreePath) -> Debruijn {
    fn _replace(
        root: Debruijn,
        replacement: Fragment,
        treepath: &TreePath,
        treepath_i: usize,
    ) -> Debruijn {
        match root {
            Debruijn::Index(index) => idx(index),
            Debruijn::Application {
                func: left,
                arg: right,
            } => match treepath.0.get(treepath_i) {
                Some(Direction::Left) => call(
                    _replace(*left, replacement, treepath, treepath_i + 1),
                    *right,
                ),
                Some(Direction::Right) => call(
                    *left,
                    _replace(*right, replacement, treepath, treepath_i + 1),
                ),
                None => replacement.0,
            },
            Debruijn::Abstraction { body } => {
                def(_replace(*body, replacement, treepath, treepath_i))
            }
        }
    }
    _replace(root, replacement, treepath, 0)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NodeIndex(usize);

#[derive(Default, Debug)]
pub struct ReductionGraph {
    nodes: Vec<Debruijn>,
    unreduced_nodes: Vec<NodeIndex>,
    edges: Vec<(NodeIndex, NodeIndex)>,
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

    fn reduce_node(&mut self, node_index: NodeIndex) {
        let index = self
            .unreduced_nodes
            .iter()
            .position(|&idx| idx == node_index)
            .unwrap();
        self.unreduced_nodes.remove(index);

        let node = &self.nodes[node_index.0];
        let reductions = get_reductions(&node);

        for reduced_node in reductions {
            let reduced_node_index = self.add_node(reduced_node);
            self.add_edge(node_index, reduced_node_index);
        }
    }

    fn any_reducible(&self) -> bool {
        !self.unreduced_nodes.is_empty()
    }
}

pub fn reduce_full(graph: &mut ReductionGraph) {
    loop {
        if graph.nodes.len() > 100 || !graph.any_reducible() {
            break;
        }
        graph.reduce_node(graph.unreduced_nodes[0]);
    }
}

fn get_reductions(term: &Debruijn) -> Vec<Debruijn> {
    treepath_filter(term, beta_reduce_if_possible)
        .into_iter()
        .map(|(treepath, reduced_fragment)| {
            replace(term.clone(), reduced_fragment.clone(), &treepath)
        })
        .collect()
}

pub fn print_nodes(graph: &ReductionGraph) {
    for (i, node) in graph.nodes.iter().enumerate() {
        println!("{}. {}", i, node);
    }
}
