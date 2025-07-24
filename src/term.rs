use std::{fmt::Display, str::FromStr};

use crate::parse;

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
    type Err = parse::ParseError;

    fn from_str(expr: &str) -> Result<Self, Self::Err> {
        let tokens = parse::tokenize(expr);
        parse::parse_program(&tokens)
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Literal(literal) => write!(f, "{}", literal.0),
            Term::Abstraction(literal, term) => write!(f, "(λ {} . {})", literal, term),
            Term::Application(term1, term2) => write!(f, "({} {})", term1, term2),
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
