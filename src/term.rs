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
        self.print(f, PrintContext::TopLevel)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PrintContext {
    TopLevel,
    InAbs,
    InAppLeft,
    InAppRight,
}

impl Term {
    fn print(&self, f: &mut fmt::Formatter<'_>, ctx: PrintContext) -> fmt::Result {
        match self {
            Term::Literal(lit) => write!(f, "{}", lit),
            // Suppose we have this program:
            // λ 1 λ 2
            // We want to distinguish the following parses
            // (λ 1) (λ 2)
            // λ (1 λ 2)
            // In the first one, we can reduce the parenthesis to this:
            // (λ 1) λ 2
            // In the second one, we can reduce to this:
            // λ 1 λ 2
            // So the only case we need parens is InAppLeft
            Term::Abstraction(arg, body) => match ctx {
                PrintContext::TopLevel | PrintContext::InAbs | PrintContext::InAppRight => {
                    write!(f, "λ{arg}.")?;
                    body.print(f, PrintContext::InAbs)
                }
                PrintContext::InAppLeft => {
                    write!(f, "(λ{arg}.")?;
                    body.print(f, PrintContext::InAbs)?;
                    write!(f, ")")
                }
            },
            // Suppose we have
            // 1 2 3
            // We need to distinguish the following parses:
            // (1 2) 3, which is the default and can be written just as 1 2 3
            // and 1 (2 3), which needs parens
            Term::Application(func, arg) => match ctx {
                PrintContext::TopLevel | PrintContext::InAbs | PrintContext::InAppLeft => {
                    func.print(f, PrintContext::InAppLeft)?;
                    write!(f, " ")?;
                    arg.print(f, PrintContext::InAppRight)
                }
                PrintContext::InAppRight => {
                    write!(f, "(")?;
                    func.print(f, PrintContext::InAppLeft)?;
                    write!(f, " ")?;
                    arg.print(f, PrintContext::InAppRight)?;
                    write!(f, ")")
                }
            },
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
