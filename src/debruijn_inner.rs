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
                Debruijn2::Abstraction { body } => _preorder_walk_mut(body, action, reverse)?,
                Debruijn2::NormalApplication { func, arg } => {
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

        match term {
            Debruijn::Index(index) => Debruijn2::Index(index),
            Debruijn::Abstraction { body } => Debruijn2::Abstraction {
                body: from_boxed(*body),
            },
            Debruijn::Application { func, arg } => Debruijn2::NormalApplication {
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
            Debruijn2::Abstraction { body } => Debruijn::Abstraction {
                body: from_boxed(*body),
            },
            Debruijn2::NormalApplication { func, arg } => Debruijn::Application {
                func: from_boxed(*func),
                arg: from_boxed(*arg),
            },
        }
    }
}

#[derive(Debug, Clone)]
pub enum Debruijn2 {
    Index(usize),
    Abstraction {
        body: Box<Debruijn2>,
    },
    NormalApplication {
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
pub struct Redex<'a> {
    pub body: &'a mut Debruijn2,
    pub arg: &'a mut Debruijn2,
}

impl<'a> TryFrom<&'a mut Debruijn2> for Redex<'a> {
    type Error = ();

    fn try_from<'b>(value: &'b mut Debruijn2) -> Result<Redex<'b>, Self::Error> {
        match value {
            Debruijn2::NormalApplication { func, arg } => match &mut **func {
                Debruijn2::Abstraction { body } => Ok(Redex { body, arg }),
                _ => Err(()),
            },
            _ => Err(()),
        }
    }
}

pub fn substitute_arg_into_body_mut(mut redex: Redex) -> Debruijn2 {
    up_one_mut(&mut redex.arg);
    let mut new_body = substitute_mut(redex);
    down_one_mut(&mut new_body);
    new_body
}

// todo: need to fix up applications that are now redexes
fn substitute_mut(mut redex: Redex) -> Debruijn2 {
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
            Debruijn2::Abstraction { body } => {
                _substitute_mut(body, match_index + 1, replacer, depth + 1);
            }
            Debruijn2::NormalApplication { func, arg } => {
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
        Debruijn2::NormalApplication { func, arg } => {
            shift_cutoff_mut(func, up_by, cutoff);
            shift_cutoff_mut(arg, up_by, cutoff);
        }
        Debruijn2::Abstraction { body } => {
            // We add one to the cutoff here because we don't want to modify bound variables
            // For example, if we're at the outer-most lambda, then any Index(1)s in the lambda body
            // are referring to that lambda's bound variable and we don't modify it.
            shift_cutoff_mut(body, up_by, cutoff + 1);
        }
    }
}
