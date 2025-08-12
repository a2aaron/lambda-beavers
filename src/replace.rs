use std::fmt::Display;

use crate::{
    debruijn::{Debruijn, call, def, idx},
    reduce::Fragment,
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
pub struct TreePath(Vec<Direction>);

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

pub fn treepath_filter2<T>(
    term: &Debruijn,
    filter_map: fn(&Debruijn, TreePath) -> Option<T>,
) -> Vec<T> {
    fn _treepath_filter<T>(
        term: &Debruijn,
        filter_map: fn(&Debruijn, TreePath) -> Option<T>,
        current_path: &mut TreePath,
        emits: &mut Vec<T>,
    ) {
        if let Some(value) = filter_map(term, current_path.clone()) {
            emits.push(value);
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

pub fn treepath_filter<T>(
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
