use std::fmt::Display;

use crate::{
    debruijn::{Debruijn, call, def, idx},
    reduce::Fragment,
};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Direction {
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
pub struct TreePath(pub Vec<Direction>);

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

#[derive(Debug, Clone, Copy)]
pub struct VisitOrder {
    emit_outermost_first: bool,
    emit_left_first: bool,
}

impl VisitOrder {
    pub const LEFT_INNERMOST: VisitOrder = VisitOrder {
        emit_outermost_first: false,
        emit_left_first: true,
    };
    pub const RIGHT_INNERMOST: VisitOrder = VisitOrder {
        emit_outermost_first: false,
        emit_left_first: false,
    };
    pub const LEFT_OUTERMOST: VisitOrder = VisitOrder {
        emit_outermost_first: true,
        emit_left_first: true,
    };
    pub const RIGHT_OUTERMOST: VisitOrder = VisitOrder {
        emit_outermost_first: true,
        emit_left_first: false,
    };
}

struct FilterContext<T> {
    filter_mapper: fn(&Debruijn, TreePath) -> Option<T>,
    current_path: TreePath,
    emits: Vec<T>,
    visit_order: VisitOrder,
}

impl<T> FilterContext<T> {
    fn new(filter_map: fn(&Debruijn, TreePath) -> Option<T>, visit_order: VisitOrder) -> Self {
        Self {
            filter_mapper: filter_map,
            current_path: TreePath(vec![]),
            emits: vec![],
            visit_order,
        }
    }

    fn emit_term(&mut self, term: &Debruijn) {
        if let Some(value) = (self.filter_mapper)(term, self.current_path.clone()) {
            self.emits.push(value);
        }
    }

    fn visit_term(&mut self, term: &Debruijn) {
        if self.visit_order.emit_outermost_first {
            self.emit_term(term);
            self.visit_inner_terms(term);
        } else {
            self.visit_inner_terms(term);
            self.emit_term(term);
        }
    }

    fn visit_inner_terms(&mut self, term: &Debruijn) {
        match term {
            Debruijn::Index(_) => (),
            Debruijn::Application { func, arg } => {
                if self.visit_order.emit_left_first {
                    self.visit_left(func);
                    self.visit_right(arg);
                } else {
                    self.visit_right(arg);
                    self.visit_left(func);
                }
            }
            Debruijn::Abstraction { body } => {
                self.visit_term(body);
            }
        }
    }

    fn visit_left(&mut self, func: &Box<Debruijn>) {
        self.current_path.0.push(Direction::Left);
        self.visit_term(&func);
        self.current_path.0.pop();
    }

    fn visit_right(&mut self, arg: &Debruijn) {
        self.current_path.0.push(Direction::Right);
        self.visit_term(&arg);
        self.current_path.0.pop();
    }
}

pub fn treepath_filter<T>(
    term: &Debruijn,
    filter_map: fn(&Debruijn, TreePath) -> Option<T>,
    visit_order: VisitOrder,
) -> Vec<T> {
    let mut ctx = FilterContext::new(filter_map, visit_order);
    ctx.visit_term(term);
    ctx.emits
}

pub fn replace(root: Debruijn, replacement: Fragment, treepath: &TreePath) -> Debruijn {
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
