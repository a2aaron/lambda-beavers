use std::{collections::HashMap, error::Error, fmt::Binary, str::FromStr};

use crate::{
    parse_debruijn, parse_term,
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
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
    // If true, then the current node is in a left application, but we have not yet emitted a
    // parenethesis for this for ambiguity purposes. This is needed because lambda-bodies are greedy
    // end extend as far to the right as possible. Therefore, if we are in the left half of an
    // application and the current term is a lambda, we need to emit parenthesis around our body
    // because we don't want the lambda to capture the terms right of the actual body
    // (which are the terms in the right half of the appliction)
    // ex: λ 1 1 can be parenthesized as (λ 1) 1 or as λ (1 1), only the first of which needs parens
    // In the first acse, we emit a parenthesis
    left_app_needs_parens: bool,
    // If true, then the current node's immediate parent is an application and the current node is
    // in the right half of that application. This is needed because right-associativity requires
    // parenthesis to disambiguate
    // Ex: 1 1 1 can be parenthesized as (1 1) 1 or as 1 (1 1), only the second of which needs parens
    right_app_immediate: bool,
}

impl Debruijn {
    fn print(&self, f: &mut fmt::Formatter<'_>, ctx: PrintContext) -> fmt::Result {
        match self {
            Debruijn::Index(i) => write!(f, "{}", i),
            Debruijn::Abstraction { body } => {
                if ctx.left_app_needs_parens {
                    // Clear the left app flag, since we no longer have any chance of being ambigious
                    let ctx = PrintContext {
                        left_app_needs_parens: false,
                        right_app_immediate: false,
                    };
                    write!(f, "(λ ")?;
                    body.print(f, ctx)?;
                    write!(f, ")")
                } else {
                    let ctx = PrintContext {
                        left_app_needs_parens: ctx.left_app_needs_parens,
                        right_app_immediate: false,
                    };
                    write!(f, "λ ")?;
                    body.print(f, ctx)
                }
            }
            Debruijn::Application { func, arg } => {
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

impl From<&str> for Debruijn {
    fn from(s: &str) -> Self {
        Debruijn::from_str(s).unwrap()
    }
}

impl From<String> for Debruijn {
    fn from(s: String) -> Self {
        Debruijn::from_str(&s).unwrap()
    }
}

impl FromStr for Debruijn {
    type Err = Box<dyn Error>;

    fn from_str(term: &str) -> Result<Self, Self::Err> {
        if term.chars().any(|c| c.is_numeric()) {
            let tokens = parse_debruijn::tokenize(term)?;
            Ok(parse_debruijn::parse_program(&tokens)?)
        } else {
            let classic_tokenized = parse_term::tokenize(term);
            let classic_parsed = parse_term::parse_program(&classic_tokenized)?;
            let debruijn = Debruijn::try_from(classic_parsed)?;
            Ok(debruijn)
        }
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

pub fn idx(a: usize) -> Debruijn {
    Debruijn::Index(a)
}

pub fn def(b: impl Into<Debruijn>) -> Debruijn {
    Debruijn::Abstraction {
        body: Box::new(b.into()),
    }
}

pub fn call(a: impl Into<Debruijn>, b: impl Into<Debruijn>) -> Debruijn {
    Debruijn::Application {
        func: Box::new(a.into()),
        arg: Box::new(b.into()),
    }
}

#[cfg(test)]
mod test {
    use crate::{
        debruijn::{Context, Debruijn, call, def, idx},
        parse_binary,
        term::Term,
        utils,
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

    impl Debruijn {
        fn is_closed_term(&self) -> bool {
            fn _is_closed_term(term: &Debruijn, depth: usize) -> bool {
                match term {
                    // eg: in λ λ λ N, the depth is 3, so we need N to be 1, 2, or 3 for it to be
                    // bound. Otherwise it's unbound.
                    Debruijn::Index(index) => *index <= depth,
                    Debruijn::Application { func, arg } => {
                        _is_closed_term(func, depth) && _is_closed_term(arg, depth)
                    }
                    Debruijn::Abstraction { body } => _is_closed_term(body, depth + 1),
                }
            }

            _is_closed_term(self, 0)
        }
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

    #[test]
    fn display_and_parse() {
        let term: Debruijn = "(1 λ 1) 1".parse().unwrap();
        let string = format!("{}", term);
        let term2: Debruijn = string.parse().unwrap();
        assert_eq!(term, term2)
    }

    #[test]
    fn bitstring_parse_to_debruijn() {
        for length in 0..=20 {
            for bitstring in utils::bitstring_permutations(length) {
                let bitstring_string: String = bitstring
                    .iter()
                    .map(|b| if *b { "1" } else { "0" })
                    .collect();
                if let Ok(binary_term) = parse_binary::from_vec(bitstring) {
                    let string = format!("{}", binary_term);
                    let normal_term: Debruijn = string.parse().unwrap();
                    assert_eq!(
                        binary_term, normal_term,
                        "terms did not match! binary {bitstring_string} -> {string} -> {normal_term}"
                    );
                }
            }
        }
    }

    #[test]
    fn bitstring_parse_to_classic_closed_only() {
        for length in 0..=20 {
            for bitstring in utils::bitstring_permutations(length) {
                let bitstring_string: String = bitstring
                    .iter()
                    .map(|b| if *b { "1" } else { "0" })
                    .collect();
                if let Ok(binary_term) = parse_binary::from_vec(bitstring) {
                    if binary_term.is_closed_term() {
                        let classic_term: Term = Term::from(&binary_term);
                        let string = format!("{}", classic_term);
                        let classic_term_reparsed: Term = string.parse().unwrap();
                        assert_eq!(
                            classic_term, classic_term_reparsed,
                            "terms did not match! binary {bitstring_string} -> {binary_term} -> {string} -> {classic_term_reparsed}"
                        );
                    }
                }
            }
        }
    }
}
