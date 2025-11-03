#![feature(iter_intersperse)]

use std::str::FromStr;

use clap::Parser;
use lambda_beaver::{debruijn::Debruijn, graphviz::Args, parse, reduce::Reducer};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    let term = args.term.clone();
    let term = match Debruijn::from_str(&term) {
        Ok(term) => term,
        Err(err) => match parse::binary::from_str(&term) {
            Ok(term) => term,
            Err(binary_err) => {
                println!("Couldn't parse {term}. Reason: {err}, {:?}", binary_err);
                std::process::exit(1);
            }
        },
    };
    let mut reducer = Reducer::new(&term);
    for _ in 0..args.reductions {
        reducer.reduce_one();
    }

    let root = if args.normalized {
        reducer.root.normalized()
    } else {
        reducer.root
    };

    let graph = lambda_beaver::graphviz::to_graph(&root, &args);
    std::fs::write(args.output.clone(), graph.to_string())?;
    Ok(())
}
