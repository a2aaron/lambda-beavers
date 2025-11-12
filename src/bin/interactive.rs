use std::{fmt::Display, str::FromStr};

use clap::Parser;
use inquire::Select;
use lambda_beavers::{
    debruijn::Debruijn,
    debruijn_flat::{self, BackingIndex, FlatTree, beta_reduce},
    parse,
    print::{NodeLabelType, PrintableTerm},
    treewalk::ChildResults,
};

#[derive(Parser, Debug)]
#[command(about, long_about = None)]
struct Args {
    /// Term to parse. This can be a classic or Debruijn term
    term: String,
    /// Node label type to use in the graphviz output
    #[arg(short, long, default_value = "debruijn")]
    node_label: NodeLabelType,
}

fn print_highlighted<'a>(tree: &'a FlatTree, highlighted: BackingIndex) -> String {
    let printable_terms = tree.postorder_walk(|_tree, ctx, results| match results {
        ChildResults::Index(binding) => {
            let index = debruijn_flat::compute_debruijn_index(&ctx.chain, binding);
            PrintableTerm::Leaf(format!("{}", index))
        }
        ChildResults::Abstraction { body_result, .. } => PrintableTerm::Abstraction {
            body_head: "λ ".to_string(),
            body: Box::new(body_result),
        },
        ChildResults::Application {
            func_result,
            arg_result,
            ..
        } => {
            let highlight = ctx.current_index() == highlighted;

            PrintableTerm::Application {
                highlight,
                func: Box::new(func_result),
                arg: Box::new(arg_result),
            }
        }
    });

    printable_terms.print()
}

enum Choice {
    Back,
    Quit,
    Reduce(usize, String),
}

impl Display for Choice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Choice::Back => write!(f, "Back"),
            Choice::Quit => write!(f, "Quit"),
            Choice::Reduce(_redex_index, highlighted) => write!(f, "{highlighted}"),
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    let term = args.term;
    let current_term = match Debruijn::from_str(&term) {
        Ok(term) => term,
        Err(err) => match parse::binary::from_str(&term) {
            Ok(term) => term,
            Err(binary_err) => {
                println!("Couldn't parse {term}. Reason: {err}, {:?}", binary_err);
                std::process::exit(1);
            }
        },
    };
    let mut current_term = FlatTree::from(&current_term);

    let mut history = vec![];

    loop {
        let redexes = current_term.get_redexes();
        let reductions: Vec<_> = redexes
            .iter()
            .enumerate()
            .map(|(redex_index, redex)| {
                // TODO: would be nice to not print out the full term if it is over 80ish characters long
                let highlighted = print_highlighted(&current_term, redex.parent_to_app.child);
                Choice::Reduce(redex_index, highlighted)
            })
            .collect();

        let mut options = vec![];
        options.extend(reductions);
        if !history.is_empty() {
            options.push(Choice::Back);
        }
        options.push(Choice::Quit);

        let message = format!("{current_term}");
        let message = if message.len() > 80 {
            let message = format!("{:b}", current_term);
            format!("len: {}", message.len())
        } else {
            message
        };
        let message = message.as_str();

        let text = Select::new(message, options).prompt()?;
        match text {
            Choice::Back => current_term = history.pop().unwrap(),
            Choice::Quit => break,
            Choice::Reduce(redex_index, _highlighted_string) => {
                history.push(current_term.clone());
                beta_reduce(&mut current_term, redexes[redex_index].clone());
            }
        }
    }
    Ok(())
}
