#![feature(iter_intersperse)]
#![feature(macro_metavar_expr_concat)]
#![feature(never_type)]
#![feature(trait_alias)]

pub mod common_terms;
pub mod debruijn;
pub mod debruijn_flat;
pub mod graph;
pub mod parse {
    pub mod binary;
    pub mod debruijn;
    pub mod term;
}
pub mod print;
pub mod reduce;
pub mod term;
pub mod treewalk;
pub mod utils;
