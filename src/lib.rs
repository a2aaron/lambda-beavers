#![feature(iter_intersperse)]
#![feature(macro_metavar_expr_concat)]
#![feature(never_type)]
#![feature(trait_alias)]
#![feature(more_float_constants)]

pub mod common_terms;
pub mod debruijn;
pub mod flat_tree;
pub mod graphviz;
pub mod reference;
pub mod parse {
    pub mod binary;
    pub mod debruijn;
    pub mod term;
}
pub mod print;
pub mod reduce;
pub mod term;
pub mod utils;
