use std::{fmt::Display, str::FromStr};

use clap::Parser;
use inquire::Select;
use lambda_beaver::{
    debruijn::{Debruijn, Root},
    parse,
    print::{NodeLabelType, PrintableTerm},
    reduce::Redex,
    replace::VisitOrder,
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

fn print_highlighted<'a>(root: &'a Root, highlighted: Redex) -> String {
    fn get_printable_terms<'a>(node: &'a Debruijn, highlighted: Redex) -> PrintableTerm {
        match node {
            Debruijn::Index(i) => PrintableTerm::Leaf(format!("{i}")),
            Debruijn::Abstraction { body } => PrintableTerm::Abstraction {
                body_head: "λ ".to_string(),
                body: Box::new(get_printable_terms(body, highlighted)),
            },
            Debruijn::Application { func, arg } => {
                let func = get_printable_terms(&func, highlighted);
                let arg = get_printable_terms(&arg, highlighted);
                let highlight = std::ptr::eq(node, highlighted.redex);

                PrintableTerm::Application {
                    highlight,
                    func: Box::new(func),
                    arg: Box::new(arg),
                }
            }
        }
    }

    let printable_terms = get_printable_terms(&root.0, highlighted);
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
    let mut current_term = Root(current_term);

    let mut history = vec![];

    loop {
        let redexes = current_term.get_redexes(VisitOrder::LEFT_OUTERMOST);
        let reductions: Vec<_> = redexes
            .iter()
            .enumerate()
            .map(|(redex_index, redex)| {
                // TODO: would be nice to not print out the full term if it is over 80ish characters long
                let highlighted = print_highlighted(&current_term, *redex);
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
                redexes[redex_index].beta_reduce(&mut current_term);
            }
        }
    }
    Ok(())
}
