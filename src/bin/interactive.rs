use std::{fmt::Display, str::FromStr};

use clap::Parser;
use inquire::Select;
use lambda_beavers::{
    beta_reduce,
    debruijn::Debruijn,
    flat_tree::{self, AbsIndex, BackingIndex, FlatTree},
    parse,
    print::{NodeLabelType, PrintableTerm},
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

fn print_highlighted(tree: &FlatTree, highlighted: BackingIndex) -> String {
    struct Context<'a> {
        tree: &'a FlatTree,
        chain: Vec<AbsIndex>,
        highlighted: BackingIndex,
    }

    fn _print_highlighted(ctx: &mut Context, index: BackingIndex) -> PrintableTerm {
        match &ctx.tree[index] {
            flat_tree::Node::FreeVar(free_var) => {
                let index = flat_tree::compute_debruijn_index_free(ctx.chain.as_slice(), free_var);
                PrintableTerm::Leaf(format!("{}", index))
            }
            flat_tree::Node::BoundVar(variable) => {
                let index = flat_tree::compute_debruijn_index_bound(
                    &ctx.tree,
                    ctx.chain.as_slice(),
                    variable,
                );
                PrintableTerm::Leaf(format!("{}", index))
            }
            flat_tree::Node::Abs(abstraction) => {
                let index = AbsIndex(index);
                ctx.chain.push(index);
                let body = _print_highlighted(ctx, abstraction.body);
                ctx.chain.pop();

                PrintableTerm::Abstraction {
                    body_head: "λ ".to_string(),
                    body: Box::new(body),
                }
            }
            flat_tree::Node::App(application) => {
                let func = _print_highlighted(ctx, application.func);
                let arg = _print_highlighted(ctx, application.arg);

                let highlight = index == ctx.highlighted;

                PrintableTerm::Application {
                    highlight,
                    func: Box::new(func),
                    arg: Box::new(arg),
                }
            }
        }
    }

    let mut ctx = Context {
        tree,
        chain: vec![],
        highlighted,
    };

    let printable_terms = _print_highlighted(&mut ctx, tree.root);
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
                let highlighted = print_highlighted(&current_term, redex.app_index);
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
                beta_reduce::beta_reduce(&mut current_term, &redexes[redex_index]);
            }
        }
    }
    Ok(())
}
