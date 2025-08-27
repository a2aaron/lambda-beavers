use std::{fmt::Display, rc::Rc, str::FromStr};

use clap::Parser;
use inquire::Select;
use lambda_beaver::{
    debruijn::Debruijn,
    graph::{Redex, get_redexes},
    parse,
    print::{NodeLabelType, PrintableTerm},
    replace::{Direction, TreePath, VisitOrder},
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

#[derive(Debug, Clone)]
struct RedexOption {
    root: Debruijn,
    redex: Redex,
}

impl RedexOption {
    fn reduced(&self) -> Debruijn {
        self.redex.beta_reduce(&self.root)
    }
}

impl Display for RedexOption {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let highlighted = print_highlighted(&self.root, &self.redex.treepath);
        write!(f, "{}", highlighted)
    }
}

fn print_highlighted(root: &Debruijn, treepath: &TreePath) -> String {
    fn get_printable_terms(
        root: &Debruijn,
        treepath: &TreePath,
        treepath_i: Option<usize>,
    ) -> PrintableTerm {
        match root {
            Debruijn::Index(i) => PrintableTerm::Leaf(format!("{i}")),
            Debruijn::Abstraction { body } => PrintableTerm::Abstraction {
                body_head: "λ ".to_string(),
                body: Box::new(get_printable_terms(body, treepath, treepath_i)),
            },
            Debruijn::Application { func, arg } => {
                let highlight = treepath_i == Some(treepath.0.len());
                let next_treepath_i = treepath_i.map(|i| i + 1);
                let (func, arg) = match treepath_i.and_then(|i| treepath.0.get(i)) {
                    Some(Direction::Left) => {
                        let func = get_printable_terms(&func, treepath, next_treepath_i);
                        let arg = get_printable_terms(&arg, treepath, None);
                        (func, arg)
                    }
                    Some(Direction::Right) => {
                        let func = get_printable_terms(&func, treepath, None);
                        let arg = get_printable_terms(&arg, treepath, next_treepath_i);
                        (func, arg)
                    }
                    None => {
                        let func = get_printable_terms(&func, treepath, None);
                        let arg = get_printable_terms(&arg, treepath, None);
                        (func, arg)
                    }
                };

                PrintableTerm::Application {
                    highlight,
                    func: Box::new(func),
                    arg: Box::new(arg),
                }
            }
        }
    }

    let printable_terms = get_printable_terms(root, treepath, Some(0));
    printable_terms.print()
}

enum Choice {
    Back,
    Quit,
    Reduce(RedexOption),
}

impl Display for Choice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Choice::Back => write!(f, "Back"),
            Choice::Quit => write!(f, "Quit"),
            Choice::Reduce(redex_option) => {
                let formatted = format!("{redex_option}");
                let out = if formatted.len() > 80 {
                    let reduced = redex_option.reduced();
                    let binary = format!("{reduced:b}");
                    format!("len = {}", binary.len())
                } else {
                    formatted
                };
                write!(f, "{out}")
            }
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
    let mut current_term = Rc::new(current_term);

    let mut history = vec![];

    loop {
        let redexes = get_redexes(&current_term, VisitOrder::LEFT_OUTERMOST);
        let reductions: Vec<_> = redexes
            .into_iter()
            .map(|redex| {
                // let reduction = redex.beta_reduce(current_term.clone());
                // args.node_label.to_string(&reduction)
                Choice::Reduce(RedexOption {
                    root: current_term.as_ref().clone(),
                    redex,
                })
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
            // todo: this should be binary length
            format!("len: {}", message.len())
        } else {
            message
        };
        let message = message.as_str();

        let text = Select::new(message, options).prompt()?;
        match text {
            Choice::Back => current_term = history.pop().unwrap(),
            Choice::Quit => break,
            Choice::Reduce(redex_option) => {
                history.push(current_term);
                current_term = Rc::new(redex_option.reduced());
            }
        }
    }
    Ok(())
}
