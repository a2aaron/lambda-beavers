#![feature(iter_intersperse)]

use std::str::FromStr;

use clap::Parser;
use lambda_beavers::{debruijn::Debruijn, graphviz::GraphvizArgs, parse, reduce::Reducer};

#[derive(Parser, Debug)]
#[command(about, long_about = None)]
pub struct Args {
    /// Term to parse. This can be a classic or Debruijn term
    pub term: String,

    /// Output file for the graphviz representation
    #[arg(short, long("out"), default_value = "out.dot")]
    pub output: String,

    #[arg(long)]
    pub reductions: usize,

    #[arg(long, default_value = "false")]
    pub normalized: bool,

    #[arg(long, default_value = "false")]
    pub no_garbage: bool,

    #[arg(long, default_value = "false")]
    pub no_color_abs: bool,

    #[arg(long, default_value = "false")]
    pub no_color_redex: bool,
}

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

    let graph_args = GraphvizArgs {
        no_garbage: args.no_garbage,
        no_color_abs: args.no_color_abs,
        no_color_redex: args.no_color_redex,
    };
    let graph = lambda_beavers::graphviz::to_graph(&root, None, &graph_args);
    std::fs::write(args.output.clone(), graph.to_string())?;
    Ok(())
}
