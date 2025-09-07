use std::ops::{ControlFlow, Index, IndexMut};

use crate::{debruijn::Debruijn, replace::VisitOrder};

impl VisitOrder {
    pub fn preorder_walk_mut_2<T>(
        &self,
        root: &mut FlatRoot,
        mut action: impl FnMut(&mut FlatRoot, Option<Parent>, TermIndex) -> ControlFlow<T>,
    ) -> Option<T> {
        fn _preorder_walk_mut<T>(
            root: &mut FlatRoot,
            parent: Option<Parent>,
            term: TermIndex,
            action: &mut impl FnMut(&mut FlatRoot, Option<Parent>, TermIndex) -> ControlFlow<T>,
            reverse: bool,
        ) -> ControlFlow<T> {
            action(root, parent, term)?;

            match root[term] {
                DebruijnNode::Index(_) => (),
                DebruijnNode::Abstraction { body, .. } => {
                    _preorder_walk_mut(root, Some(Parent::Body(term)), body, action, reverse)?
                }
                DebruijnNode::Application { func, arg } => {
                    if reverse {
                        _preorder_walk_mut(root, Some(Parent::Arg(term)), arg, action, reverse)?;
                        _preorder_walk_mut(root, Some(Parent::Func(term)), func, action, reverse)?;
                    } else {
                        _preorder_walk_mut(root, Some(Parent::Func(term)), func, action, reverse)?;
                        _preorder_walk_mut(root, Some(Parent::Arg(term)), arg, action, reverse)?;
                    }
                }
            }
            ControlFlow::Continue(())
        }

        _preorder_walk_mut(root, None, root.root, &mut action, self.reverse).break_value()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlatRoot {
    backing: Vec<DebruijnNode>,
    root: TermIndex,
}
impl FlatRoot {
    // Clone the given subtree. The returned value points to the newly allocated subtree.
    fn clone_subtree(&mut self, term: TermIndex) -> TermIndex {
        match self[term] {
            DebruijnNode::Index(index) => self.alloc_one(Some(DebruijnNode::Index(index))),
            DebruijnNode::Abstraction { body, usage } => {
                let abs = self.alloc_one(None);
                let body = self.clone_subtree(body);
                self[abs] = DebruijnNode::Abstraction { body, usage };
                abs
            }
            DebruijnNode::Application { func, arg } => {
                let app = self.alloc_one(None);
                let func = self.clone_subtree(func);
                let arg = self.clone_subtree(arg);

                self[app] = DebruijnNode::Application { func, arg };
                app
            }
        }
    }

    fn alloc_one(&mut self, term: Option<DebruijnNode>) -> TermIndex {
        // If none, then alloc a dummy node, this should be fixed up afterwards
        let term = term.unwrap_or(DebruijnNode::Index(TermIndex::MAX));
        let term_index = self.backing.len();
        self.backing.push(term);
        term_index
    }
}

impl Index<TermIndex> for FlatRoot {
    type Output = DebruijnNode;

    fn index(&self, index: TermIndex) -> &Self::Output {
        &self.backing[index]
    }
}

impl IndexMut<TermIndex> for FlatRoot {
    fn index_mut(&mut self, index: TermIndex) -> &mut Self::Output {
        &mut self.backing[index]
    }
}

impl<T> From<T> for FlatRoot
where
    T: Into<Debruijn>,
{
    fn from(term: T) -> Self {
        fn flatten(root: &mut FlatRoot, term: Debruijn) -> TermIndex {
            match term {
                Debruijn::Index(index) => root.alloc_one(Some(DebruijnNode::Index(index))),
                Debruijn::Abstraction { body } => {
                    let usage = compute_usage(&body);
                    let abs = root.alloc_one(None);
                    let body = flatten(root, *body);
                    root[abs] = DebruijnNode::Abstraction { body, usage };
                    abs
                }
                Debruijn::Application { func, arg } => {
                    let app = root.alloc_one(None);
                    let func = flatten(root, *func);
                    let arg = flatten(root, *arg);
                    root[app] = DebruijnNode::Application { func, arg };
                    app
                }
            }
        }

        let mut root = FlatRoot {
            backing: vec![],
            root: 0,
        };
        flatten(&mut root, term.into());
        root
    }
}

impl From<&FlatRoot> for Debruijn {
    fn from(root: &FlatRoot) -> Self {
        fn _from(root: &FlatRoot, term: TermIndex) -> Debruijn {
            match root[term] {
                DebruijnNode::Index(index) => Debruijn::Index(index),
                DebruijnNode::Abstraction { body, .. } => Debruijn::Abstraction {
                    body: Box::new(_from(root, body)),
                },
                DebruijnNode::Application { func, arg } => Debruijn::Application {
                    func: Box::new(_from(root, func)),
                    arg: Box::new(_from(root, arg)),
                },
            }
        }

        _from(root, root.root)
    }
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

/// Computes the number of usages that the first free variable appears in the body of an abstraction.
/// (that is to say, this function computes the number times the input variable appears in the
/// `body` must be the body of the abstraction!
/// ter the body of an abstraction
/// eg: in λ 1 λ 2 λ 3, we have that 1, 2, and 3 all refer to the same variable, so the usage is 3
fn compute_usage_flat(root: &FlatRoot, body: TermIndex) -> usize {
    fn _compute_usage(root: &FlatRoot, term_i: TermIndex, depth: usize) -> usize {
        match root[term_i] {
            DebruijnNode::Index(index) => (index == depth) as usize,
            DebruijnNode::Application { func, arg } => {
                _compute_usage(root, func, depth) + _compute_usage(root, arg, depth)
            }
            DebruijnNode::Abstraction { body, .. } => _compute_usage(root, body, depth + 1),
        }
    }
    // Because this is the body of an abstraction, we actually are starting at depth 1
    // (so Index(1) refers to the input variable). If we had started at top-level (or had
    // the abstraction itself as input rather than it's body), then this would be 0.
    _compute_usage(root, body, 1)
}

// The index for the DebruijnNode::Index variant. This is an index for the actual lambda term and works
// just like how Debruijn::Index works.
type DebruijnIndex = usize;

// The index for a given DebruijnNode when inside of a FlatRoot
type TermIndex = usize;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum DebruijnNode {
    Index(DebruijnIndex),
    Abstraction {
        body: TermIndex,
        /// Number of times the input argument is used in the body
        /// If this is zero, then when doing argument substitution, the algorithm can just
        /// return the body and throw away the argument!
        /// This value is constant over the lifetime of the Abstraction (this will become not true if
        /// we do "partial" substition where not all usages of the input argument are substituted)
        usage: usize,
    },
    Application {
        func: TermIndex,
        arg: TermIndex,
    },
}

impl std::fmt::Debug for DebruijnNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Index(index) => write!(f, "idx@{}", *index),
            Self::Abstraction { body, usage } => {
                write!(f, "abs: body -> {} (usage={})", *body, *usage)
            }
            Self::Application { func, arg } => write!(f, "app: func -> {}, arg -> {}", *func, *arg),
        }
    }
}

impl Default for DebruijnNode {
    fn default() -> Self {
        DebruijnNode::Index(0)
    }
}

/// Represents the parent of a given DebruijnNode. The TermIndex in each variant points to the parent
/// node (and not the child node). In methods which take Option<Parent>, generally None indicates that
/// a term is the root of the lambda term and therefore has no parent.
#[derive(Debug, Clone, Copy)]
pub enum Parent {
    /// Indicates that the parent is an Abstraction and the child is pointed to
    /// by the parent's `body` field.
    Body(TermIndex),
    /// Indicates that the parent is an Application and the child is pointed to
    /// by the parent's `func` field.
    Func(TermIndex),
    /// Indicates that the parent is an Application and the child is pointed to
    /// by the parent's `arg` field.
    Arg(TermIndex),
}

#[derive(Debug)]
pub struct RedexMut {
    // Term that this redex is a child of. If this is none, then the Redex is actually the root (and therefore is
    // pointed to by FlatRoot.root)
    parent: Option<Parent>,
    // The Abstraction containing the body. This must be an Abstraction
    abs: TermIndex,
    // The body of the Abstraction. This must be pointed to by `abs`
    body: TermIndex,
    // The argument of the Application. This must be pointed to by `app.arg`
    arg: TermIndex,
    // The usage of the `body`. Provided for convinence
    usage: usize,
}

impl RedexMut {
    pub fn try_get(terms: &FlatRoot, parent: Option<Parent>, app: TermIndex) -> Option<RedexMut> {
        match terms[app] {
            DebruijnNode::Application { func, arg } => match terms[func] {
                DebruijnNode::Abstraction { body, usage } => Some(RedexMut {
                    parent,
                    abs: func,
                    body,
                    arg,
                    usage,
                }),
                _ => None,
            },
            _ => None,
        }
    }
}

pub fn substitute_arg_into_body_mut(root: &mut FlatRoot, redex: RedexMut) {
    // Before this, we have the following shape of tree:
    //   parent
    //     |
    //     V
    //    app
    //   /   \
    //  V     V
    // abs   arg
    //  |
    //  V
    // body

    // After this, we would like the following:
    //   parent------+
    //               |
    //               |
    //    app        |
    //   /   \       |
    //  V     V      |
    // abs   arg     |
    //               |
    //               |
    // body <--------+
    //  ||
    //  VV
    // [various copies of arg]

    // This will cause app, abs, and the entire arg subtree to become garbage
    // Note that we can actually avoid arg from becoming garbage if we re-use it's allocation (assuming
    // it is ever actually used in body). However this is not implemented at time of writing

    if redex.usage == 0 {
        // Fix up the indicies in it to account for the fact that we are still dropping out the abstraction that the body is in.
        down_one_mut(root, redex.body);
        // No need to do anything with the argument because it is never used in the body
        // Instead, just point the term to the body.
        repoint_node(root, redex.parent, redex.body);
        // Since the argument is not used, the entire arg subtree is garbage now.
    } else {
        // Otherwise, perform substitution as usual
        // We need to first fix up the argument indicies since we are entering into an abstraction
        up_one_mut(root, redex.arg);

        // Then perform the actual substition on body.
        // This may end up causing abs's body to get repointed if the redex body consists of a
        // single leaf node that gets substituted.
        let (parent, new_body) = substitute_mut(root, redex);

        // Then, fix down the (potentially new body) indicies, since we are dropping out the abstraction
        // (We target abs because body may be junk now.)
        down_one_mut(root, new_body);

        // Finally, make the parent point to the body, causing `app` and `abs` to be garbage.
        repoint_node(root, parent, new_body);
    };
    // The app and abs nodes are no longer pointed to by anything, and therefore are now garbage.
}

/// Repoint the term at `child` so that it is the child of `parent`. This does not affect the
/// existing parent (which means that the child should either be an orphan--eg: has no existing parent
/// or is root).
/// If `parent` is none, then the child is made the root node of `root`.
fn repoint_node(root: &mut FlatRoot, parent: Option<Parent>, child: TermIndex) {
    match parent {
        Some(Parent::Body(parent)) => {
            let DebruijnNode::Abstraction { .. } = root[parent] else {
                unreachable!(
                    "Expected abstraction, got {:?} at {} in {:#?}",
                    root[parent], parent, root
                )
            };
            root[parent] = DebruijnNode::Abstraction {
                body: child,
                usage: compute_usage_flat(root, child),
            }
        }
        Some(Parent::Func(parent)) => {
            let DebruijnNode::Application { arg, .. } = root[parent] else {
                unreachable!(
                    "Expected application, got {:?} at {} in {:#?}",
                    root[parent], parent, root
                )
            };
            root[parent] = DebruijnNode::Application { func: child, arg };
        }
        Some(Parent::Arg(parent)) => {
            let DebruijnNode::Application { func, .. } = root[parent] else {
                unreachable!(
                    "Expected application, got {:?} at {} in {:#?}",
                    root[parent], parent, root
                )
            };
            root[parent] = DebruijnNode::Application { func, arg: child }
        }
        // Root
        None => {
            root.root = child;
            return;
        }
    };
}

// Substitute new copies of the arg into the body.
// Each time the argument is subsituted, a clone of it is allocated and fixed up. Then the leaf
// node being substituted has it's parent repointed to the new argument subtree (with the leaf
// becoming garbage)
// Note that this means if the redex body consists of a single leaf node that gets substituted
// (so it's parent node is the redex abs), then redex.abs gets repointed and the body is garbage now
// Hence, to help with this, the return value of this method is the location of the redex.abs's body,
// (which is either a newly allocated arg subtree or the existing body)
fn substitute_mut(root: &mut FlatRoot, redex: RedexMut) -> (Option<Parent>, TermIndex) {
    fn _substitute_mut(
        root: &mut FlatRoot,
        parent: Parent,
        term: TermIndex,
        redex_arg: TermIndex,
        match_index: usize,
        depth: usize,
    ) {
        match root[term] {
            DebruijnNode::Index(term_index) => {
                if term_index == match_index {
                    // TODO: Optimization opportunity: Instead of making `arg` become garbage, instead
                    // reuse it and avoid doing one alloc.
                    let last_arg_allocation = false;

                    let new_arg = if !last_arg_allocation {
                        root.clone_subtree(redex_arg)
                    } else {
                        redex_arg
                    };
                    // Bump up free variables by `depth`
                    up_by_mut(root, new_arg, depth);
                    repoint_node(root, Some(parent), new_arg);
                }
            }
            DebruijnNode::Abstraction { body, .. } => {
                _substitute_mut(
                    root,
                    Parent::Body(term),
                    body,
                    redex_arg,
                    match_index + 1,
                    depth + 1,
                );
            }
            DebruijnNode::Application { func, arg } => {
                _substitute_mut(
                    root,
                    Parent::Func(term),
                    func,
                    redex_arg,
                    match_index,
                    depth,
                );
                _substitute_mut(root, Parent::Arg(term), arg, redex_arg, match_index, depth);
            }
        }
    }
    _substitute_mut(root, Parent::Body(redex.abs), redex.body, redex.arg, 1, 0);

    let DebruijnNode::Abstraction { body, .. } = root[redex.abs] else {
        unreachable!(
            "expected abstraction, got {:?} at {} in {root:#?}",
            root[redex.abs], redex.abs
        );
    };
    (redex.parent, body)
}

fn up_by_mut(root: &mut FlatRoot, term: TermIndex, up_by: usize) {
    shift_cutoff_mut(root, term, up_by as isize, 1)
}

// ↑ n = n         if n < cutoff
//       n + up_by otherwise
// ↑ λ t = λ (↑ t) where up_by -> up_by and cutoff -> cutoff + 1
// ↑ (t1 t2) = (↑ t1) (↑ t2)
fn up_one_mut(root: &mut FlatRoot, term: TermIndex) {
    shift_cutoff_mut(root, term, 1, 1)
}

fn down_one_mut(root: &mut FlatRoot, term: TermIndex) {
    shift_cutoff_mut(root, term, -1, 1)
}

/// Shift the indicies for all terms up by an amount. Indicies below the cutoff are not modified
/// This is useful during beta reduction because we need to "drop out" an abstraction.
fn shift_cutoff_mut(root: &mut FlatRoot, term: TermIndex, up_by: isize, cutoff: usize) {
    match root[term] {
        DebruijnNode::Index(term_index) => {
            // Recall that an index starts at 1, so if cutoff is set to 1, then this branch will always be taken.
            if term_index >= cutoff {
                let new_index = term_index.checked_add_signed(up_by).unwrap();
                root.backing[term] = DebruijnNode::Index(new_index);
            }
        }
        DebruijnNode::Application { func, arg } => {
            shift_cutoff_mut(root, func, up_by, cutoff);
            shift_cutoff_mut(root, arg, up_by, cutoff);
        }
        DebruijnNode::Abstraction { body, .. } => {
            // We add one to the cutoff here because we don't want to modify bound variables
            // For example, if we're at the outer-most lambda, then any Index(1)s in the lambda body
            // are referring to that lambda's bound variable and we don't modify it.
            shift_cutoff_mut(root, body, up_by, cutoff + 1);
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

    fn compile(term: &str) -> FlatRoot {
        FlatRoot::from(Debruijn::from_str(term).unwrap())
    }

    #[test]
    fn flattening_trivial_idx() {
        let original = Debruijn::from("0");
        let actual = FlatRoot::from(original);
        let expected = FlatRoot {
            backing: vec![DebruijnNode::Index(0)],
            root: 0,
        };
        assert_eq!(actual, expected)
    }

    #[test]
    fn flattening_trivial_abs() {
        let original = Debruijn::from("λ 1");
        let actual = FlatRoot::from(original);
        let expected = FlatRoot {
            backing: vec![
                DebruijnNode::Abstraction { body: 1, usage: 1 },
                DebruijnNode::Index(1),
            ],
            root: 0,
        };
        assert_eq!(actual, expected)
    }

    #[test]
    fn flattening_trivial_abs_2() {
        let original = Debruijn::from("λ λ 1");
        let actual = FlatRoot::from(original);
        let expected = FlatRoot {
            backing: vec![
                DebruijnNode::Abstraction { body: 1, usage: 0 },
                DebruijnNode::Abstraction { body: 2, usage: 1 },
                DebruijnNode::Index(1),
            ],
            root: 0,
        };
        assert_eq!(actual, expected)
    }

    #[test]
    fn flattening_trivial_app() {
        let original = Debruijn::from("1 2");
        let actual = FlatRoot::from(original);
        let expected = FlatRoot {
            backing: vec![
                DebruijnNode::Application { func: 1, arg: 2 },
                DebruijnNode::Index(1),
                DebruijnNode::Index(2),
            ],
            root: 0,
        };
        assert_eq!(actual, expected)
    }

    #[test]
    fn flattening_trivial_app_2() {
        let original = Debruijn::from("(1 2) (3 4)");
        let actual = FlatRoot::from(original);
        let expected = FlatRoot {
            backing: vec![
                DebruijnNode::Application { func: 1, arg: 4 }, // 0
                DebruijnNode::Application { func: 2, arg: 3 }, // 1
                DebruijnNode::Index(1),                        // 2
                DebruijnNode::Index(2),                        // 3
                DebruijnNode::Application { func: 5, arg: 6 }, // 4
                DebruijnNode::Index(3),                        // 5
                DebruijnNode::Index(4),                        // 6
            ],
            root: 0,
        };
        assert_eq!(actual, expected)
    }

    #[test]
    fn round_trip() {
        let original = Debruijn::from("(λ λ λ 3 1 (2 1)) ((λ λ 2) (λ λ λ 3 1 (2 1))) λ λ 2");
        let flat = FlatRoot::from(original.clone());
        let roundtripped = Debruijn::from(&flat);

        assert_eq!(
            original, roundtripped,
            "Expected {original}, got {roundtripped}",
        );
    }

    #[test]
    fn usage_zero() {
        let mut root = compile("(λ 2) (λ 50)");

        let redex = RedexMut::try_get(&root, None, 0).unwrap();
        assert_eq!(redex.usage, 0);

        substitute_arg_into_body_mut(&mut root, redex);

        let expected = compile("1");

        let actual = Debruijn::from(&root);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }

    #[test]
    fn usage_one() {
        let mut root = compile("(λ 1) (λ 50)");

        let redex = RedexMut::try_get(&mut root, None, 0).unwrap();
        assert_eq!(redex.usage, 1);

        substitute_arg_into_body_mut(&mut root, redex);

        let expected = compile("λ 50");

        let actual = Debruijn::from(&root);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }

    #[test]
    fn body_is_leaf() {
        let mut root = compile("(λ 1) (1 2 3 4)");

        let redex = RedexMut::try_get(&mut root, None, 0).unwrap();
        assert_eq!(redex.usage, 1);

        substitute_arg_into_body_mut(&mut root, redex);

        let expected = compile("1 2 3 4");

        let actual = Debruijn::from(&root);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }

    #[test]
    fn body_is_not_leaf() {
        let mut root = compile("(λ λ 2) (1 2 3 4)");

        let redex = RedexMut::try_get(&mut root, None, 0).unwrap();
        assert_eq!(redex.usage, 1);

        substitute_arg_into_body_mut(&mut root, redex);

        let expected = compile("λ 2 3 4 5");

        let actual = Debruijn::from(&root);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }

    #[test]
    fn usage_many() {
        let mut root = compile("(λ 1 λ 2 λ 3 λ 4) 100");

        let redex = RedexMut::try_get(&mut root, None, 0).unwrap();
        assert_eq!(redex.usage, 4);

        substitute_arg_into_body_mut(&mut root, redex);

        let expected = compile("100 λ 101 λ 102 λ 103");

        let actual = Debruijn::from(&root);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }
}
