#![feature(iter_intersperse)]
#![feature(hash_set_entry)]
#![feature(macro_metavar_expr_concat)]
#![feature(type_alias_impl_trait)]
#![feature(never_type)]
#![feature(trait_alias)]

pub mod common_terms;
pub mod debruijn;
pub mod graph;
pub mod parse {
    pub mod binary;
    pub mod debruijn;
    pub mod term;
}
pub mod print;
pub mod reduce;
pub mod replace;
pub mod term;
pub mod utils;
