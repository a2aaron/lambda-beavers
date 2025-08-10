use std::fmt::{self, Display};

use crate::{debruijn::Debruijn, term::Term};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PrintContext {
    // If true, then the current node is in a left application, but we have not yet emitted a
    // parenethesis for this for ambiguity purposes. This is needed because lambda-bodies are greedy
    // end extend as far to the right as possible. Therefore, if we are in the left half of an
    // application and the current term is a lambda, we need to emit parenthesis around our body
    // because we don't want the lambda to capture the terms right of the actual body
    // (which are the terms in the right half of the appliction)
    // ex: λ 1 1 can be parenthesized as (λ 1) 1 or as λ (1 1), only the first of which needs parens
    // In the first case, we emit a parenthesis
    left_app_needs_parens: bool,
    // If true, then the current node's immediate parent is an application and the current node is
    // in the right half of that application. This is needed because right-associativity requires
    // parenthesis to disambiguate
    // Ex: 1 1 1 can be parenthesized as (1 1) 1 or as 1 (1 1), only the second of which needs parens
    right_app_immediate: bool,
}

impl PrintContext {
    fn new() -> PrintContext {
        PrintContext {
            left_app_needs_parens: false,
            right_app_immediate: false,
        }
    }
    fn abs_not_parens(&self) -> PrintContext {
        PrintContext {
            left_app_needs_parens: self.left_app_needs_parens,
            right_app_immediate: false,
        }
    }

    fn abs_parens(&self) -> PrintContext {
        PrintContext {
            // Clear the left app flag, since we no longer have any chance of being ambigious“
            left_app_needs_parens: false,
            right_app_immediate: false,
        }
    }

    fn left_app(&self) -> PrintContext {
        PrintContext {
            // Set the left app flag, since terms inside of it may need parenethsization to
            // avoid being ambigious.
            left_app_needs_parens: true,
            right_app_immediate: false,
        }
    }

    fn right_app(&self) -> PrintContext {
        PrintContext {
            left_app_needs_parens: self.left_app_needs_parens,
            right_app_immediate: true,
        }
    }
}

impl Display for Debruijn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.print(f, PrintContext::new())
    }
}

impl Debruijn {
    fn print(&self, f: &mut fmt::Formatter<'_>, ctx: PrintContext) -> fmt::Result {
        match self {
            Debruijn::Index(i) => write!(f, "{}", i),
            Debruijn::Abstraction { body } => {
                if ctx.left_app_needs_parens {
                    write!(f, "(λ ")?;
                    body.print(f, ctx.abs_parens())?;
                    write!(f, ")")
                } else {
                    write!(f, "λ ")?;
                    body.print(f, ctx.abs_not_parens())
                }
            }
            Debruijn::Application { func, arg } => {
                if ctx.right_app_immediate {
                    write!(f, "(")?;
                }
                func.print(f, ctx.left_app())?;
                write!(f, " ")?;
                arg.print(f, ctx.right_app())?;
                if ctx.right_app_immediate {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.print(f, PrintContext::new())
    }
}

impl Term {
    fn print(&self, f: &mut fmt::Formatter<'_>, ctx: PrintContext) -> fmt::Result {
        match self {
            Term::Literal(literal) => write!(f, "{literal}"),
            Term::Abstraction { arg, body } => {
                if ctx.left_app_needs_parens {
                    write!(f, "(λ{arg}.")?;
                    body.print(f, ctx.abs_parens())?;
                    write!(f, ")")
                } else {
                    write!(f, "λ{arg}.")?;
                    body.print(f, ctx.abs_not_parens())
                }
            }
            Term::Application { func, arg } => {
                if ctx.right_app_immediate {
                    write!(f, "(")?;
                }
                func.print(f, ctx.left_app())?;
                write!(f, " ")?;
                arg.print(f, ctx.right_app())?;
                if ctx.right_app_immediate {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{debruijn::Debruijn, parse::binary, term::Term, utils};

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
                if let Ok(binary_term) = binary::from_vec(bitstring) {
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
                if let Ok(binary_term) = binary::from_vec(bitstring) {
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
