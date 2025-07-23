use std::fmt::Display;

/// A literal
/// TODO: This should eventually become more sophisticated, possibly containing
/// references to some manager struct that knows about all literals. For now, this can
/// just be a string
#[derive(Debug, Clone, PartialEq, Eq)]
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

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Literal(literal) => write!(f, "{}", literal.0),
            Term::Abstraction(literal, term) => write!(f, "(λ {} . {})", literal, term),
            Term::Application(term1, term2) => write!(f, "({} {})", term1, term2),
        }
    }
}

// Helper method to create a Literal
pub fn lit(lit: impl Into<Literal>) -> Term {
    Term::Literal(lit.into())
}

// Helper method to create a lambda abstraction
pub fn def(input: impl Into<Literal>, term: Term) -> Term {
    Term::Abstraction(input.into(), Box::new(term))
}

// Helper method to create a function application
pub fn call(term1: Term, term2: Term) -> Term {
    Term::Application(Box::new(term1), Box::new(term2))
}
