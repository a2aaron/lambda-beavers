use std::ops::ControlFlow;

use crate::{
    debruijn::{Debruijn, Root},
    replace::VisitOrder,
};
impl VisitOrder {
    pub fn preorder_walk_mut_2<T>(
        &self,
        root: &mut Root2,
        mut action: impl FnMut(&mut Debruijn2) -> ControlFlow<T>,
    ) -> Option<T> {
        fn _preorder_walk_mut<T>(
            term: &mut Debruijn2,
            action: &mut impl FnMut(&mut Debruijn2) -> ControlFlow<T>,
            reverse: bool,
        ) -> ControlFlow<T> {
            action(term)?;

            match term {
                Debruijn2::Index(_) => (),
                Debruijn2::Abstraction { body, .. } => _preorder_walk_mut(body, action, reverse)?,
                Debruijn2::Application { func, arg } => {
                    if reverse {
                        _preorder_walk_mut(arg, action, reverse)?;
                        _preorder_walk_mut(func, action, reverse)?;
                    } else {
                        _preorder_walk_mut(func, action, reverse)?;
                        _preorder_walk_mut(arg, action, reverse)?;
                    }
                }
            }
            ControlFlow::Continue(())
        }

        _preorder_walk_mut(&mut root.0, &mut action, self.reverse).break_value()
    }
}

#[derive(Debug, Clone)]
pub struct Root2(Debruijn2);

impl From<Root> for Root2 {
    fn from(value: Root) -> Self {
        Root2(Debruijn2::from(value.0))
    }
}

impl From<Root2> for Root {
    fn from(value: Root2) -> Self {
        Root(Debruijn::from(value.0))
    }
}

impl From<Debruijn> for Debruijn2 {
    fn from(term: Debruijn) -> Self {
        fn from_boxed(term: Debruijn) -> Box<Debruijn2> {
            Box::new(Debruijn2::from(term))
        }

        /// Computes the number of usages that the first free variable appears in the body of an abstraction.
        /// (that is to say, this function computes the number times the input variable appears in the
        /// `body` must be the body of the abstraction!
        /// ter the body of an abstraction
        /// eg: in λ 1 λ 2 λ 3, we have that 1, 2, and 3 all refer to the same variable, so the usage is 3
        fn compute_usage(body: &Debruijn) -> usize {
            fn _compute_usage(term: &Debruijn, depth: usize) -> usize {
                match term {
                    Debruijn::Index(index) => (*index == depth) as usize,
                    Debruijn::Application { func, arg } => {
                        _compute_usage(&func, depth) + _compute_usage(&arg, depth)
                    }
                    Debruijn::Abstraction { body, .. } => _compute_usage(body, depth + 1),
                }
            }
            // Because this is the body of an abstraction, we actually are starting at depth 1
            // (so Index(1) refers to the input variable). If we had started at top-level (or had
            // the abstraction itself as input rather than it's body), then this would be 0.
            _compute_usage(body, 1)
        }

        match term {
            Debruijn::Index(index) => Debruijn2::Index(index),
            Debruijn::Abstraction { body } => Debruijn2::Abstraction {
                usage: compute_usage(body.as_ref()),
                body: from_boxed(*body),
            },
            Debruijn::Application { func, arg } => Debruijn2::Application {
                func: from_boxed(*func),
                arg: from_boxed(*arg),
            },
        }
    }
}

impl From<Debruijn2> for Debruijn {
    fn from(term: Debruijn2) -> Self {
        fn from_boxed(term: Debruijn2) -> Box<Debruijn> {
            Box::new(Debruijn::from(term))
        }
        match term {
            Debruijn2::Index(index) => Debruijn::Index(index),
            Debruijn2::Abstraction { body, .. } => Debruijn::Abstraction {
                body: from_boxed(*body),
            },
            Debruijn2::Application { func, arg } => Debruijn::Application {
                func: from_boxed(*func),
                arg: from_boxed(*arg),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Debruijn2 {
    Index(usize),
    Abstraction {
        body: Box<Debruijn2>,
        /// Number of times the input argument is used in the body
        /// If this is zero, then when doing argument substitution, the algorithm can just
        /// return the body and throw away the argument!
        /// This value is constant over the lifetime of the Abstraction (this will become not true if
        /// we do "partial" substition where not all usages of the input argument are substituted)
        usage: usize,
    },
    Application {
        func: Box<Debruijn2>,
        arg: Box<Debruijn2>,
    },
}

impl Default for Debruijn2 {
    fn default() -> Self {
        Debruijn2::Index(0)
    }
}

#[derive(Debug)]
pub struct RedexMut<'a> {
    body: &'a mut Debruijn2,
    arg: &'a mut Debruijn2,
    usage: usize,
}

impl<'a> TryFrom<&'a mut Debruijn2> for RedexMut<'a> {
    type Error = ();

    fn try_from<'b>(value: &'b mut Debruijn2) -> Result<RedexMut<'b>, Self::Error> {
        match value {
            Debruijn2::Application { func, arg } => match &mut **func {
                Debruijn2::Abstraction { body, usage } => Ok(RedexMut {
                    body,
                    arg,
                    usage: *usage,
                }),
                _ => Err(()),
            },
            _ => Err(()),
        }
    }
}

pub fn substitute_arg_into_body_mut(mut redex: RedexMut) -> Debruijn2 {
    if redex.usage == 0 {
        // No need to do anything with the argument because it is never used in the body
        // Instead, just return the body and fix up the indicies in it to account for the fact that
        // we are still dropping out the abstraction that the body is in.
        let mut new_body = std::mem::take(redex.body);
        down_one_mut(&mut new_body);
        new_body
    } else {
        // Otherwise, perform substitution as usual
        // We need to first fix up the argument indicies since we are entering into an abstraction
        up_one_mut(&mut redex.arg);
        // Then perform the actual substition
        let mut new_body = substitute_mut(redex);
        // Finally, fix down the (new) body indicies, since we are dropping out the abstraction
        down_one_mut(&mut new_body);
        new_body
    }
}

fn substitute_mut(mut redex: RedexMut) -> Debruijn2 {
    fn _substitute_mut(
        term: &mut Debruijn2,
        match_index: usize,
        replacer: &Debruijn2,
        depth: usize,
    ) {
        match term {
            Debruijn2::Index(term_index) => {
                if *term_index == match_index {
                    // Bump up free variables by `depth`
                    let mut replacer = replacer.clone();
                    up_by_mut(&mut replacer, depth);
                    *term = replacer;
                }
            }
            Debruijn2::Abstraction { body, .. } => {
                _substitute_mut(body, match_index + 1, replacer, depth + 1);
            }
            Debruijn2::Application { func, arg } => {
                _substitute_mut(func, match_index, replacer, depth);
                _substitute_mut(arg, match_index, replacer, depth);
            }
        }
    }
    _substitute_mut(&mut redex.body, 1, &redex.arg, 0);
    std::mem::take(redex.body)
}

fn up_by_mut(term: &mut Debruijn2, up_by: usize) {
    shift_cutoff_mut(term, up_by as isize, 1)
}

// ↑ n = n         if n < cutoff
//       n + up_by otherwise
// ↑ λ t = λ (↑ t) where up_by -> up_by and cutoff -> cutoff + 1
// ↑ (t1 t2) = (↑ t1) (↑ t2)
fn up_one_mut(term: &mut Debruijn2) {
    shift_cutoff_mut(term, 1, 1)
}

fn down_one_mut(term: &mut Debruijn2) {
    shift_cutoff_mut(term, -1, 1)
}

/// Shift the indicies for all terms up by an amount. Indicies below the cutoff are not modified
/// This is useful during beta reduction because we need to "drop out" an abstraction.
fn shift_cutoff_mut(term: &mut Debruijn2, up_by: isize, cutoff: usize) {
    match term {
        Debruijn2::Index(term_index) => {
            // Recall that an index starts at 1, so if cutoff is set to 1, then this branch will always be taken.
            if *term_index >= cutoff {
                *term_index = term_index.checked_add_signed(up_by).unwrap();
            }
        }
        Debruijn2::Application { func, arg } => {
            shift_cutoff_mut(func, up_by, cutoff);
            shift_cutoff_mut(arg, up_by, cutoff);
        }
        Debruijn2::Abstraction { body, .. } => {
            // We add one to the cutoff here because we don't want to modify bound variables
            // For example, if we're at the outer-most lambda, then any Index(1)s in the lambda body
            // are referring to that lambda's bound variable and we don't modify it.
            shift_cutoff_mut(body, up_by, cutoff + 1);
        }
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    macro_rules! mario {
        () => {
            use super::*;
        };
    }

    mario!();
    use crate::debruijn::Debruijn;

    fn compile(term: &str) -> Debruijn2 {
        Debruijn2::from(Debruijn::from_str(term).unwrap())
    }

    #[test]
    fn no_usage() {
        let mut redex = compile("(λ 2) (λ 50)");

        let redex = RedexMut::try_from(&mut redex).unwrap();
        assert_eq!(redex.usage, 0);

        let new_body = substitute_arg_into_body_mut(redex);

        let expected = compile("1");
        assert_eq!(new_body, expected);
    }

    #[test]
    fn one_usage() {
        let mut redex = compile("(λ 1) (λ 50)");

        let redex = RedexMut::try_from(&mut redex).unwrap();
        assert_eq!(redex.usage, 1);

        let new_body = substitute_arg_into_body_mut(redex);

        let expected = compile("λ 50");
        assert_eq!(new_body, expected);
    }
}
