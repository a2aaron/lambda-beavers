#![feature(iter_intersperse)]

mod debruijn;
mod parse;
mod reduce;
mod term;

use std::str::FromStr;

use parse::{parse_program, pretty, tokenize};

use crate::{
    debruijn::{call, def, idx, Debruijn},
    term::Term,
};

fn debug(program: &str) {
    println!("RAW   : {}", program);
    let tokens = tokenize(program);
    println!("TOKENS: {}", pretty(&tokens));
    match parse_program(&tokens) {
        Ok(program) => println!("PARSED: {}", program),
        Err(err) => println!("ERROR : {:?}", err),
    }
    println!("--------")
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum Direction {
    Left,
    Right,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TreePath(Vec<Direction>);

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

fn beta_reduce_if_possible(term: &Debruijn) -> Option<Fragment> {
    match term {
        Debruijn::Application { func, arg } => match &**func {
            Debruijn::Abstraction { body } => Some(Fragment(reduce::__beta_reduce(body, arg))),
            _ => None,
        },
        _ => None,
    }
}

fn replace(root: Debruijn, replacement: Fragment, mut treepath: TreePath) -> Debruijn {
    match root {
        Debruijn::Index(index) => idx(index),
        Debruijn::Application {
            func: left,
            arg: right,
        } => match treepath.0.pop() {
            Some(direction) => {
                let (left, right) = if direction == Direction::Left {
                    (replace(*left, replacement, treepath), *right)
                } else {
                    (*left, replace(*right, replacement, treepath))
                };

                call(left, right)
            }
            None => replacement.0,
        },
        Debruijn::Abstraction { body } => def(replace(*body, replacement, treepath)),
    }
}

struct ReductionNode {
    term: Debruijn,
    reductions: Vec<ReductionNode>,
}

fn get_reductions(term: &Debruijn) -> Vec<Debruijn> {
    treepath_filter(term, beta_reduce_if_possible)
        .into_iter()
        .map(|(treepath, reduced_fragment)| replace(term.clone(), reduced_fragment, treepath))
        .collect()
}

fn to_reduction_node(term: Debruijn) -> ReductionNode {
    let reductions = get_reductions(&term)
        .into_iter()
        .map(|reduction| to_reduction_node(reduction))
        .collect();
    ReductionNode { term, reductions }
}

fn print_tree(term: &Debruijn) {
    fn _print_tree(node: &ReductionNode, depth: usize) {
        let indent = format!("{}", "  ".repeat(depth * 2));
        println!("{}{}", indent, node.term);
        for node in &node.reductions {
            _print_tree(&node, depth + 1);
        }
    }
    let node = to_reduction_node(term.clone());
    _print_tree(&node, 0);
}

fn main() {
    let ident_term = compile("λx.x");
    let true_term = compile("λx.λy.x");
    let false_term = compile("λx.λy.y");
    let and_term = compile("λp.λq.p q p");
    let plus_term = compile("λm.λn.λf.λx.m f (n f x)");
    let three_term = compile("λf.λx.f (f (f x))");
    let four_term = compile("λf.λx.f (f (f (f x)))");
    let five_term = compile("λf.λx.f (f (f (f (f x))))");

    println!("IDENT = {}", ident_term);
    println!("TRUE = {}", true_term);
    println!("FALSE = {}", false_term);
    println!("AND = {}", and_term);
    println!("PLUS = {}", plus_term);
    println!("THREE = {}", three_term);
    println!("FIVE = {}", five_term);
    // let combined = call(call(plus_term, three_term), five_term);
    // println!("PLUS THREE FIVE = {}", combined);
    let combined = call(call(and_term, true_term), false_term);
    println!("AND TRUE FALSE = {}", combined);
    println!("---");

    print_tree(&combined);
}

fn compile(arg: &str) -> Debruijn {
    let term = Term::from_str(arg).unwrap();
    let debruijn = Debruijn::try_from(term).unwrap();
    debruijn
}
