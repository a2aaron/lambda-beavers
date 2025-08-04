#![feature(iter_intersperse)]
#![feature(hash_set_entry)]
#![feature(macro_metavar_expr_concat)]
#![feature(type_alias_impl_trait)]
#![feature(never_type)]

pub mod common_terms;
pub mod debruijn;
pub mod graph;
pub mod parse_binary;
pub mod parse_debruijn;
pub mod parse_term;
pub mod reduce;
pub mod replace;
pub mod term;
pub mod utils;
