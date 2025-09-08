use std::{fmt::Display, str::FromStr};

use crate::{debruijn::Debruijn, debruijn_inner::FlatRoot, parse::term};

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
    Abstraction { arg: Literal, body: Box<Term> },
    Application { func: Box<Term>, arg: Box<Term> },
}

impl FromStr for Term {
    type Err = term::ParseError;

    fn from_str(term: &str) -> Result<Self, Self::Err> {
        let tokens = term::tokenize(term);
        term::parse_program(&tokens)
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
        let n = self.variables.len();
        let letter = alphabet.chars().nth(n % alphabet.len()).unwrap();
        let subscript = n / alphabet.len();
        let literal = if subscript > 0 {
            Literal(format!("{letter}{}", subscript - 1))
        } else {
            Literal(letter.to_string())
        };
        self.variables.push(literal.clone());
        literal
    }

    fn pop_variable(&mut self) {
        self.variables.pop();
    }
}

impl From<FlatRoot> for Term {
    fn from(root: FlatRoot) -> Self {
        Term::from(Debruijn::from(&root))
    }
}
impl From<&FlatRoot> for Term {
    fn from(root: &FlatRoot) -> Self {
        Term::from(Debruijn::from(root))
    }
}
impl From<Debruijn> for Term {
    fn from(debruijn: Debruijn) -> Self {
        Term::from(&debruijn)
    }
}
impl From<&Debruijn> for Term {
    fn from(debruijn: &Debruijn) -> Self {
        from_debruijn(debruijn, &mut Context::new())
    }
}

// Turn a Debruijn term into a classic Term.
// depth refers to how many layers of
fn from_debruijn(debruijn: &Debruijn, ctx: &mut Context) -> Term {
    match debruijn {
        Debruijn::Index(index) => lit(ctx.get(*index).unwrap_or_else(|| {
            // Indicies which are greater than the current depth are unbound.
            // Note that they can end up refering to the same values.
            // Eg: in λ (λ (λ 4) 3) 2, all of these refer to the same unbound variable
            // (which would be named unbound_1 in this case)
            let depth = ctx.variables.len();
            assert!(*index > depth);
            let unbound_name = format!("u_{}", index - depth).into();
            unbound_name
        })),
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
    Term::Abstraction {
        arg: i.into(),
        body: Box::new(b.into()),
    }
}

// Helper method to create a function application
pub fn call(a: impl Into<Term>, b: impl Into<Term>) -> Term {
    Term::Application {
        func: Box::new(a.into()),
        arg: Box::new(b.into()),
    }
}
