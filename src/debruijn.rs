use std::{collections::HashMap, fmt::Binary, str::FromStr};

use crate::{
    parse_debruijn,
    term::{Literal, Term},
};
use std::fmt;

/// A Debruijn term.
/// Note that this notation is 1-indexed.
/// So λx.x = λ 1
/// More examples
/// λx.x = λ 1
/// λz.z = λ 1
/// λx.λy.x = λ λ 2
/// λx.λy.λs.λz.x s (y s z) = λ λ λ λ 4 2 (3 2 1)
/// (λx.x x) (λx.x x) = (λ 1 1) (λ 1 1)
/// (λx.λx.x) (λ y.y) = (λ λ 1) (λ 1)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Debruijn {
    Index(usize),
    Application {
        func: Box<Debruijn>,
        arg: Box<Debruijn>,
    },
    Abstraction {
        body: Box<Debruijn>,
    },
}

impl Binary for Debruijn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Debruijn::Index(index) => write!(f, "{}0", "1".repeat(*index)),
            Debruijn::Application { func, arg } => write!(f, "01{:b}{:b}", **func, **arg),
            Debruijn::Abstraction { body } => write!(f, "00{:b}", **body),
        }
    }
}

impl fmt::Display for Debruijn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Debruijn::Index(i) => write!(f, "{}", i),
            Debruijn::Abstraction { body } => write!(f, "(λ {})", body),
            Debruijn::Application { func, arg } => write!(f, "({} {})", func, arg),
        }
    }
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
        Debruijn::Application {
            func: Box::new(a.into()),
            arg: Box::new(b.into()),
        }
    }
}

impl FromStr for Debruijn {
    type Err = parse_debruijn::ParseError;

    fn from_str(term: &str) -> Result<Self, Self::Err> {
        let tokens = parse_debruijn::tokenize(term)?;
        parse_debruijn::parse_program(&tokens)
    }
}

impl TryFrom<Term> for Debruijn {
    type Error = String;

    fn try_from(term: Term) -> Result<Self, Self::Error> {
        compile(term, &mut Context::default())
    }
}

/// Compile a term. Note that if there are any free variables (that is, a variable
/// which does not appear in the binding of an Abstraction in the term), then it
/// needs to be bound in the Context object.
pub fn compile(term: Term, ctx: &mut Context) -> Result<Debruijn, String> {
    let term = match term {
        Term::Literal(literal) => match ctx.get_index(literal.clone()) {
            Some(index) => idx(index),
            None => return Err(format!("unbound variable {}", literal)),
        },
        Term::Abstraction(literal, term) => {
            ctx.push_literal(literal.clone());
            let term = compile(*term, ctx)?;
            ctx.pop_literal(literal);
            def(term)
        }
        Term::Application(term1, term2) => {
            let term1 = compile(*term1, ctx)?;
            let term2 = compile(*term2, ctx)?;
            call(term1, term2)
        }
    };
    Ok(term)
}

#[derive(Default, Debug, Clone)]
pub struct Context {
    variable_to_level: HashMap<Literal, Vec<usize>>,
    current_depth: usize,
}

impl Context {
    pub fn push_literal(&mut self, literal: impl Into<Literal>) {
        self.variable_to_level
            .entry(literal.into())
            .or_default()
            .push(self.current_depth);
        self.current_depth += 1;
    }
    fn pop_literal(&mut self, literal: impl Into<Literal>) {
        self.variable_to_level
            .get_mut(&literal.into())
            .unwrap()
            .pop();
        self.current_depth -= 1;
    }

    fn get_index(&self, literal: Literal) -> Option<usize> {
        let level = *self.variable_to_level.get(&literal)?.last()?;
        Some(self.current_depth - level)
    }
}

impl<L, const N: usize> From<[L; N]> for Context
where
    L: Into<Literal>,
{
    fn from(literals: [L; N]) -> Self {
        let mut ctx = Context::default();
        for literal in literals {
            ctx.push_literal(literal);
        }
        ctx
    }
}

#[allow(dead_code)]
pub fn idx(a: usize) -> Debruijn {
    Debruijn::Index(a)
}

#[allow(dead_code)]
pub fn def(b: impl Into<Debruijn>) -> Debruijn {
    Debruijn::Abstraction {
        body: Box::new(b.into()),
    }
}

#[allow(dead_code)]
pub fn call(a: impl Into<Debruijn>, b: impl Into<Debruijn>) -> Debruijn {
    Debruijn::Application {
        func: Box::new(a.into()),
        arg: Box::new(b.into()),
    }
}

#[cfg(test)]
mod test {
    use crate::{
        debruijn::{call, def, idx, Context, Debruijn},
        term::Term,
    };

    macro_rules! assert_compile {
        ($input:expr, $expected:expr) => {{
            let term: Term = $input.parse().unwrap();
            let actual = term.try_into().unwrap();
            assert_eq!($expected, actual);
        }};
    }

    macro_rules! assert_compile_with_context {
        ($input:expr, $expected:expr, $ctx:expr) => {{
            let term: Term = $input.parse().unwrap();
            let actual = crate::debruijn::compile(term, &mut $ctx).unwrap();
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
    fn convert_i_is_for_identity() {
        assert_compile!("λx.x", def(1));
    }

    #[test]
    fn convert_k_is_for_konstant() {
        assert_compile!("λx. λy. x", def(def(2)));
    }

    #[test]
    fn convert_s_is_for_substitution() {
        assert_compile!("λx. λy. λz. x z (y z)", def(def(def(((3, 1), (2, 1))))));
    }

    #[test]
    fn convert_w_is_for_wikipedia() {
        let input = "λwikipedia. (λthe. the (λfree. free)) (λfree. wikipedia free) ";
        let expected = def((def((1, def(1))), def((2, 1))));
        assert_compile!(input, expected)
    }

    #[test]
    fn convert_shadowed() {
        let input = "λx.(λx.x) x";
        let expected = def((def(1), 1));
        assert_compile!(input, expected)
    }

    #[test]
    fn convert_example() {
        let input = "λx.λy.(λu.λv.u x) y";
        let expected = def(def((def(def((2, 4))), 1)));
        assert_compile!(input, expected)
    }

    #[test]
    fn convert_example2() {
        let input = "λy.λx.(λu.λv.u x) y";
        let expected = def(def((def(def((2, 3))), 2)));
        assert_compile!(input, expected)
    }

    #[test]
    fn convert_example3() {
        let input = "λw.(λx.λy.λz.x y z) w";
        let expected = def((def(def(def(((3, 2), 1)))), 1));
        assert_compile!(input, expected)
    }

    #[test]
    fn convert_fail_unbound_trivial() {
        assert_invalid!("x")
    }

    #[test]
    fn convert_fail_unbound() {
        assert_invalid!("λa.λb.a c")
    }

    #[test]
    fn convert_fail_previously_bound() {
        assert_invalid!("(λx.x) x")
    }

    #[test]
    fn convert_ok_unbound_trivial() {
        let mut ctx = Context::from(["a"]);
        assert_compile_with_context!("a", idx(1), ctx);
    }

    #[test]
    fn convert_ok_unbound_in_context() {
        let mut ctx = Context::from(["b"]);
        assert_compile_with_context!("λa.b", def(2), ctx);
    }

    #[test]
    fn convert_ok_unbound_multi() {
        let mut ctx = Context::from(["d", "a", "b"]);
        assert_compile_with_context!("λc.d", def(4), ctx);
    }

    #[test]
    fn convert_ok_unbound_andbound() {
        let mut ctx = Context::from(["a"]);
        let expected = call(1, def(def(1)));
        assert_compile_with_context!("a λb.λa.a", expected, ctx);
    }

    #[test]
    fn print_binary() {
        let term = def(def(def(((1, 3), 2))));
        assert_compile!("λx.λy.λz.z x y", term);

        let binary = format!("{:b}", term);
        assert_eq!("0000000101101110110", binary);
    }
}
