use std::collections::HashMap;

use crate::term::{Literal, Term};

#[derive(Debug, PartialEq, Eq)]
pub enum Debruijn {
    Index(usize),
    Application(Box<Debruijn>, Box<Debruijn>),
    Abstraction(Box<Debruijn>),
}

impl From<usize> for Debruijn {
    fn from(value: usize) -> Self {
        Debruijn::Index(value)
    }
}

impl<A, B> From<(A, B)> for Debruijn
where
    A: Into<Debruijn>,
    B: Into<Debruijn>,
{
    fn from((a, b): (A, B)) -> Self {
        Debruijn::Application(Box::new(a.into()), Box::new(b.into()))
    }
}

impl TryFrom<Term> for Debruijn {
    type Error = String;

    fn try_from(term: Term) -> Result<Self, Self::Error> {
        to_debruijn(term, &mut Context::default())
    }
}

fn to_debruijn(term: Term, ctx: &mut Context) -> Result<Debruijn, String> {
    let term = match term {
        Term::Literal(literal) => match ctx.get_index(literal.clone()) {
            Some(index) => Debruijn::Index(index),
            None => return Err(format!("unbound variable {}", literal)),
        },
        Term::Abstraction(literal, term) => {
            ctx.push_literal(literal.clone());
            let term = to_debruijn(*term, ctx)?;
            ctx.pop_literal(literal);
            Debruijn::Abstraction(Box::new(term))
        }
        Term::Application(term1, term2) => {
            let term1 = to_debruijn(*term1, ctx)?;
            let term2 = to_debruijn(*term2, ctx)?;
            Debruijn::Application(Box::new(term1), Box::new(term2))
        }
    };
    Ok(term)
}

#[derive(Default)]
pub struct Context {
    variable_to_level: HashMap<Literal, Vec<usize>>,
    current_depth: usize,
}

impl Context {
    fn push_literal(&mut self, literal: Literal) {
        self.variable_to_level
            .entry(literal)
            .or_default()
            .push(self.current_depth);
        self.current_depth += 1;
    }
    fn pop_literal(&mut self, literal: Literal) {
        self.variable_to_level.get_mut(&literal).unwrap().pop();
        self.current_depth -= 1;
    }

    fn get_index(&self, literal: Literal) -> Option<usize> {
        let level = *self.variable_to_level.get(&literal)?.last()?;
        Some(self.current_depth - level)
    }
}

#[cfg(test)]
mod test {
    use crate::{debruijn::Debruijn, term::Term};

    fn def(b: impl Into<Debruijn>) -> Debruijn {
        Debruijn::Abstraction(Box::new(b.into()))
    }

    macro_rules! assert_compile {
        ($input:expr, $expected:expr) => {{
            let term: Term = $input.parse().unwrap();
            let actual = term.try_into().unwrap();
            assert_eq!($expected, actual);
        }};
    }

    macro_rules! assert_invalid {
        ($input:expr) => {{
            let term: Term = $input.parse().unwrap();
            let actual = Debruijn::try_from(term);
            assert!(actual.is_err())
        }};
    }

    #[test]
    fn test_convert_i_is_for_identity() {
        assert_compile!("λx.x", def(1));
    }

    #[test]
    fn test_convert_k_is_for_konstant() {
        assert_compile!("λx. λy. x", def(def(2)));
    }

    #[test]
    fn test_convert_s_is_for_substitution() {
        assert_compile!("λx. λy. λz. x z (y z)", def(def(def(((3, 1), (2, 1))))));
    }

    #[test]
    fn test_convert_w_is_for_wikipedia() {
        let input = "λwikipedia. (λthe. the (λfree. free)) (λfree. wikipedia free) ";
        let expected = def((def((1, def(1))), def((2, 1))));
        assert_compile!(input, expected)
    }

    #[test]
    fn test_convert_fail_unbound_trivial() {
        assert_invalid!("x")
    }

    #[test]
    fn test_convert_fail_unbound() {
        assert_invalid!("λa.λb.a c")
    }

    #[test]
    fn test_convert_fail_previously_bound() {
        assert_invalid!("(λx.x) x")
    }
}
