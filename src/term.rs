use std::{
    fmt::{self, Display},
    str::FromStr,
};

use crate::{debruijn::Debruijn, parse_term};

/// A literal
/// TODO: This should eventually become more sophisticated, possibly containing
/// references to some manager struct that knows about all literals. For now, this can
/// just be a string
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Literal(pub String);
impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<&str> for Literal {
    fn from(value: &str) -> Self {
        Literal(value.to_string())
    }
}

impl From<String> for Literal {
    fn from(value: String) -> Self {
        Literal(value)
    }
}

/// A term in the lambda calculus.
#[derive(Debug, PartialEq, Eq)]
pub enum Term {
    Literal(Literal),
    Abstraction(Literal, Box<Term>),
    Application(Box<Term>, Box<Term>),
}

impl FromStr for Term {
    type Err = parse_term::ParseError;

    fn from_str(term: &str) -> Result<Self, Self::Err> {
        let tokens = parse_term::tokenize(term);
        parse_term::parse_program(&tokens)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.print(
            f,
            PrintContext {
                left_app_needs_parens: false,
                right_app_immediate: false,
            },
        )
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PrintContext {
    left_app_needs_parens: bool,
    right_app_immediate: bool,
}

impl Term {
    fn print(&self, f: &mut fmt::Formatter<'_>, ctx: PrintContext) -> fmt::Result {
        match self {
            Term::Literal(literal) => write!(f, "{literal}"),
            Term::Abstraction(arg, body) => {
                if ctx.left_app_needs_parens {
                    // Clear the left app flag, since we no longer have any chance of being ambigious
                    let ctx = PrintContext {
                        left_app_needs_parens: false,
                        right_app_immediate: false,
                    };
                    write!(f, "(λ{arg}.")?;
                    body.print(f, ctx)?;
                    write!(f, ")")
                } else {
                    let ctx = PrintContext {
                        left_app_needs_parens: ctx.left_app_needs_parens,
                        right_app_immediate: false,
                    };
                    write!(f, "λ{arg}.")?;
                    body.print(f, ctx)
                }
            }
            Term::Application(func, arg) => {
                // Set the left app flag, since terms inside of it may need parenethsization to
                // avoid being ambigious.
                let func_ctx = PrintContext {
                    left_app_needs_parens: true,
                    right_app_immediate: false,
                };
                let arg_ctx = PrintContext {
                    left_app_needs_parens: ctx.left_app_needs_parens,
                    right_app_immediate: true,
                };

                if ctx.right_app_immediate {
                    write!(f, "(")?;
                    func.print(f, func_ctx)?;
                    write!(f, " ")?;
                    arg.print(f, arg_ctx)?;
                    write!(f, ")")
                } else {
                    func.print(f, func_ctx)?;
                    write!(f, " ")?;
                    arg.print(f, arg_ctx)
                }
            }
        }
    }
}

impl From<&str> for Term {
    fn from(value: &str) -> Self {
        lit(value)
    }
}

impl From<String> for Term {
    fn from(value: String) -> Self {
        lit(value)
    }
}

impl<A, B> From<(A, B)> for Term
where
    A: Into<Term>,
    B: Into<Term>,
{
    fn from((a, b): (A, B)) -> Self {
        call(a, b)
    }
}

struct Context {
    variables: Vec<Literal>,
}
impl Context {
    fn new() -> Context {
        Context { variables: vec![] }
    }

    fn get(&self, index: usize) -> Option<Literal> {
        self.variables.iter().rev().nth(index - 1).cloned()
    }

    fn push_variable(&mut self) -> Literal {
        let alphabet = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        let literal = alphabet.chars().nth(self.variables.len()).unwrap();
        let literal = Literal(literal.to_string());
        self.variables.push(literal.clone());
        literal
    }

    fn pop_variable(&mut self) {
        self.variables.pop();
    }
}

impl From<&Debruijn> for Term {
    fn from(debruijn: &Debruijn) -> Self {
        from_debruijn(debruijn, &mut Context::new())
    }
}

fn from_debruijn(debruijn: &Debruijn, ctx: &mut Context) -> Term {
    match debruijn {
        Debruijn::Index(index) => lit(ctx
            .get(*index)
            // TODO: this ends up rebinding unbound vars to different values even if they should be the same...
            .unwrap_or_else(|| format!("unbound_{index}").into())),
        Debruijn::Application { func, arg } => {
            call(from_debruijn(&func, ctx), from_debruijn(&arg, ctx))
        }
        Debruijn::Abstraction { body } => {
            let literal = ctx.push_variable();
            let term = def(literal, from_debruijn(&body, ctx));
            ctx.pop_variable();
            term
        }
    }
}

// Helper method to create a Literal
pub fn lit(l: impl Into<Literal>) -> Term {
    Term::Literal(l.into())
}

// Helper method to create a lambda abstraction
pub fn def(i: impl Into<Literal>, b: impl Into<Term>) -> Term {
    Term::Abstraction(i.into(), Box::new(b.into()))
}

// Helper method to create a function application
pub fn call(a: impl Into<Term>, b: impl Into<Term>) -> Term {
    Term::Application(Box::new(a.into()), Box::new(b.into()))
}
