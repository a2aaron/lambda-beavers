use core::fmt;
use std::{
    fmt::{Binary, Display},
    ops::{ControlFlow, Index, IndexMut},
    str::FromStr,
};

use crate::{debruijn::Debruijn, treewalk::VisitOrder};

impl VisitOrder {
    pub fn preorder_walk_2<T>(
        &self,
        root: &FlatRoot,
        mut action: impl FnMut(&FlatRoot, TermWithParent) -> ControlFlow<T>,
    ) -> Option<T> {
        fn _preorder_walk<T>(
            root: &FlatRoot,
            term: TermWithParent,
            action: &mut impl FnMut(&FlatRoot, TermWithParent) -> ControlFlow<T>,
            reverse: bool,
        ) -> ControlFlow<T> {
            action(root, term)?;

            let term = term.term;
            match root[term] {
                DebruijnNode::Index(_) => (),
                DebruijnNode::Abstraction { body, .. } => {
                    let body = TermWithParent::body(term, body);
                    _preorder_walk(root, body, action, reverse)?
                }
                DebruijnNode::Application { func, arg } => {
                    let arg = TermWithParent::arg(term, arg);
                    let func = TermWithParent::func(term, func);
                    if reverse {
                        _preorder_walk(root, arg, action, reverse)?;
                        _preorder_walk(root, func, action, reverse)?;
                    } else {
                        _preorder_walk(root, func, action, reverse)?;
                        _preorder_walk(root, arg, action, reverse)?;
                    }
                }
            }
            ControlFlow::Continue(())
        }

        _preorder_walk(root, TermWithParent::root(root), &mut action, self.reverse).break_value()
    }

    pub fn preorder_walk_mut_2<T>(
        &self,
        root: &mut FlatRoot,
        mut action: impl FnMut(&mut FlatRoot, TermWithParent) -> ControlFlow<T>,
    ) -> Option<T> {
        fn _preorder_walk<T>(
            root: &mut FlatRoot,
            term: TermWithParent,
            action: &mut impl FnMut(&mut FlatRoot, TermWithParent) -> ControlFlow<T>,
            reverse: bool,
        ) -> ControlFlow<T> {
            action(root, term)?;

            let term = term.term;
            match root[term] {
                DebruijnNode::Index(_) => (),
                DebruijnNode::Abstraction { body, .. } => {
                    let body = TermWithParent::body(term, body);
                    _preorder_walk(root, body, action, reverse)?
                }
                DebruijnNode::Application { func, arg } => {
                    let arg = TermWithParent::arg(term, arg);
                    let func = TermWithParent::func(term, func);
                    if reverse {
                        _preorder_walk(root, arg, action, reverse)?;
                        _preorder_walk(root, func, action, reverse)?;
                    } else {
                        _preorder_walk(root, func, action, reverse)?;
                        _preorder_walk(root, arg, action, reverse)?;
                    }
                }
            }
            ControlFlow::Continue(())
        }

        _preorder_walk(root, TermWithParent::root(root), &mut action, self.reverse).break_value()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FlatRoot {
    pub backing: Vec<DebruijnNode>,
    pub root: TermIndex,
}
impl FlatRoot {
    fn new() -> FlatRoot {
        FlatRoot {
            backing: vec![],
            root: TermIndex(0),
        }
    }

    /// Allocate the given term onto the backing vector. If none is passed, then a dummy node is
    /// allocated, which should be modified by the caller. Otherwise, the node is set to the node
    /// in the input `term`.
    /// The return value is the index to the newly allocated node.
    fn alloc_one(&mut self, term: Option<DebruijnNode>) -> TermIndex {
        // If none, then alloc a dummy node, this should be fixed up afterwards
        let term = term.unwrap_or(DebruijnNode::Index(DebruijnIndex::MAX));
        let term_index = TermIndex(self.backing.len());
        self.backing.push(term);
        term_index
    }

    pub fn is_bnf(&self) -> bool {
        let result = VisitOrder::LEFT_OUTERMOST.preorder_walk_2(self, |root, term| {
            if RedexMut::try_get(root, term).is_some() {
                ControlFlow::Break(false)
            } else {
                ControlFlow::Continue(())
            }
        });
        result.unwrap_or(true)
    }

    pub fn get_redexes(&self, visit_order: VisitOrder) -> Vec<RedexMut> {
        let mut redexes = vec![];
        visit_order.preorder_walk_2(self, |root, term| {
            if let Some(redex) = RedexMut::try_get(root, term) {
                redexes.push(redex);
            }
            ControlFlow::Continue::<()>(())
        });
        redexes
    }

    pub fn normalized(&self) -> FlatRoot {
        fn _clone(old_root: &FlatRoot, new_root: &mut FlatRoot, term: TermIndex) -> TermIndex {
            match old_root[term] {
                DebruijnNode::Index(idx) => {
                    let idx = DebruijnNode::Index(idx);
                    new_root.alloc_one(Some(idx))
                }
                DebruijnNode::Abstraction { body, usage } => {
                    let abs = new_root.alloc_one(None);
                    let body = _clone(old_root, new_root, body);
                    new_root[abs] = DebruijnNode::Abstraction { body, usage };
                    abs
                }
                DebruijnNode::Application { func, arg } => {
                    let app = new_root.alloc_one(None);
                    let func = _clone(old_root, new_root, func);
                    let arg = _clone(old_root, new_root, arg);
                    new_root[app] = DebruijnNode::Application { func, arg };
                    app
                }
            }
        }

        let mut new_root = FlatRoot::new();
        _clone(self, &mut new_root, self.root);
        new_root
    }

    pub fn check_usage(&self) -> Result<(), (TermIndex, usize, usize)> {
        fn _check_usage(root: &FlatRoot, term: TermIndex) -> Result<(), (TermIndex, usize, usize)> {
            match root[term] {
                DebruijnNode::Abstraction { body, usage } => {
                    _check_usage(root, body)?;
                    let actual = compute_usage_flat(root, body);
                    let expected = usage;
                    if actual != expected {
                        Err((term, actual, expected))
                    } else {
                        Ok(())
                    }
                }
                DebruijnNode::Index(_) => Ok(()),
                DebruijnNode::Application { func, arg } => {
                    _check_usage(root, func)?;
                    _check_usage(root, arg)?;
                    Ok(())
                }
            }
        }
        _check_usage(&self, self.root)
    }
}

impl FromStr for FlatRoot {
    type Err = <Debruijn as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(FlatRoot::from(&Debruijn::from_str(s)?))
    }
}

impl Display for FlatRoot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&Debruijn::from(self), f)
    }
}

impl Binary for FlatRoot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Binary::fmt(&Debruijn::from(self), f)
    }
}

impl Index<TermIndex> for FlatRoot {
    type Output = DebruijnNode;

    fn index(&self, index: TermIndex) -> &Self::Output {
        &self.backing[index.0]
    }
}

impl IndexMut<TermIndex> for FlatRoot {
    fn index_mut(&mut self, index: TermIndex) -> &mut Self::Output {
        &mut self.backing[index.0]
    }
}

impl From<Vec<DebruijnNode>> for FlatRoot {
    fn from(backing: Vec<DebruijnNode>) -> Self {
        FlatRoot {
            backing,
            root: TermIndex(0),
        }
    }
}

impl From<Debruijn> for FlatRoot {
    fn from(value: Debruijn) -> Self {
        FlatRoot::from(&value)
    }
}

impl From<&Debruijn> for FlatRoot {
    fn from(term: &Debruijn) -> Self {
        fn flatten(root: &mut FlatRoot, term: &Debruijn) -> TermIndex {
            match term {
                Debruijn::Index(index) => root.alloc_one(Some(DebruijnNode::Index(*index))),
                Debruijn::Abstraction { body } => {
                    let usage = compute_usage(&body);
                    let abs = root.alloc_one(None);
                    let body = flatten(root, body);
                    root[abs] = DebruijnNode::Abstraction { body, usage };
                    abs
                }
                Debruijn::Application { func, arg } => {
                    let app = root.alloc_one(None);
                    let func = flatten(root, func);
                    let arg = flatten(root, arg);
                    root[app] = DebruijnNode::Application { func, arg };
                    app
                }
            }
        }

        let mut root = FlatRoot::new();
        flatten(&mut root, term);
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
    fn _compute_usage(term: &Debruijn, depth: DebruijnDepth) -> usize {
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
    fn _compute_usage(root: &FlatRoot, term_i: TermIndex, depth: DebruijnDepth) -> usize {
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

// The depth relative to some term. This is used to determine if a variable is free within a term
// If a given Index node has a DebruijnIndex >= DebruijnDepth, then that Index node is a free variable
// with respect to that )
type DebruijnDepth = usize;

// The index for the DebruijnNode::Index variant. This is an index for the actual lambda term and works
// just like how Debruijn::Index works.
type DebruijnIndex = usize;

// The index for a given DebruijnNode when inside of a FlatRoot
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TermIndex(pub usize);

impl Display for TermIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TermWithParent {
    pub term: TermIndex,
    parent: Option<Parent>,
}
impl TermWithParent {
    fn body(abs: TermIndex, body: TermIndex) -> TermWithParent {
        TermWithParent {
            term: body,
            parent: Some(Parent::Body(abs)),
        }
    }

    fn func(app: TermIndex, func: TermIndex) -> TermWithParent {
        TermWithParent {
            term: func,
            parent: Some(Parent::Func(app)),
        }
    }

    fn arg(app: TermIndex, arg: TermIndex) -> TermWithParent {
        TermWithParent {
            term: arg,
            parent: Some(Parent::Arg(app)),
        }
    }

    fn root(root: &FlatRoot) -> TermWithParent {
        TermWithParent {
            term: root.root,
            parent: None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct RedexMut {
    // Application term for the redex. If the parent for this is none,
    // then the Redex is actually the root (and therefore is pointed to by FlatRoot.root)
    app: TermWithParent,
    // The Abstraction containing the body. This must be an Abstraction
    pub abs: TermIndex,
    // The body of the Abstraction. This must be pointed to by `abs`
    body: TermWithParent,
    // The argument of the Application. This must be pointed to by `app.arg`
    arg: TermIndex,
    // The usage of the `body`. Provided for convinence
    usage: usize,
}

impl RedexMut {
    pub fn try_get(root: &FlatRoot, app: TermWithParent) -> Option<RedexMut> {
        match root[app.term] {
            DebruijnNode::Application { func, arg } => match root[func] {
                DebruijnNode::Abstraction { body, usage } => {
                    let body = TermWithParent::body(func, body);
                    let redex = RedexMut {
                        app,
                        abs: func,
                        body,
                        arg,
                        usage,
                    };
                    Some(redex)
                }
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

    // Some notes on how usage changes
    // First, defining usage: Usage is a property of abstractions. A given abstraction binds a particular
    // variable to itself, which I will call the bound variable.
    // The usage of an abstraction is the number of times the bound variable appears in the body of
    // the abstraction. The usage is a natural number and can be zero.
    // As an example, in λa.λb.b, there are two abstractions. The first one binds a (λa) and the second
    // one binds b (λb). For the first one, it's usage is zero because a does not appear in the body
    // of λa. For the second one, it's usage is one because b appears once in the body.
    //
    // We can also talk about the usage of an abstraction in a given subterm.
    // Consider this: λa.(λb.a b) (λc.a a).
    // The usage of a in λb is one, while the usage of a in λc is two.
    // In addition, the usage of b in λc and the usage of c in λb are both zero.
    // (We might say that, in the first paragraph, we were talking about "the usage of a in λa"
    // or "the usage of b in λb")

    // There are two things we care about that may change during substitution:
    // - child abstractions in body (incl body itself)
    // - parent abstractions in parent (incl parent itself)
    // Notably, the usages for body and it's children do not change because we are substituting arg
    // into body. arg cannot possibly capture
    // aany variables in the body subtree, since arg isn't in said subtree. Therefore, none of the
    // body usages change.
    // The parent-chain can have it's usage change, but fortunately this is easy to compute.
    // Suppose we have parent abstraction λx
    // Let's say that the usage of args in the body is A
    // and the usage of x in the args is B
    // then, when redex evaluation is done, args will be substituted into the body A times
    // Each time it is, we will get another copy of args containing B uses of x
    // This results in A * B usages getting added
    // Then, when we drop out the original args subtree, we lose B uses of x
    // This results in a total change of A * B - B = (A - 1) * B uses of x.
    //
    // This explains the behavior of
    // few different cases such as:
    // 1. If the usage of args in the body is 0, then the usage of x will decrease by B
    //    because (0 - 1) * B = -B
    // 2. If the usage of args in the body is 1, then the usage of x remains constant
    //    because (1 - 1) * B = 0 * B = 0
    // 3. If the usage of x in args is 0, then the usage of x remains constant
    //    because (A - 1) * 0 = 0
    // (Moreover, if the (total) usage of x is 0, then after evaluation, the usage of x remains
    // zero.)

    if redex.usage == 0 {
        // Fix up the indicies in it to account for the fact that we are still dropping out the abstraction that the body is in.
        down_one_mut(root, redex.body.term);
        // No need to do anything with the argument because it is never used in the body
        // Instead, just point the term to the body.
        repoint_node(root, redex.app.parent, redex.body.term);
        // Since the argument is not used, the entire arg subtree is garbage now.
    } else {
        // Otherwise, perform substitution as usual

        // Perform the actual substition on body.
        // This method actually fuses the fixing down/up that needs to happen for the whole body
        // in addition to performing substitutions.
        // This may end up causing abs's body to get repointed if the redex body consists of a
        // single leaf node that gets substituted.
        let new_body = substitute_and_fix_body_mut(root, redex);

        // Finally, make the parent point to the body, causing `app` and `abs` to be garbage.
        repoint_node(root, redex.app.parent, new_body);
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

// This substitutes indicies that point to the implicit lambda that `function_body` is
// part of.
// Consider, for example, where we want to subsitute into λ 0 1 2, sow e have function body = 0 1 2.
// in this case, 0 would be replaced by `replacer`. Note that we need to track depth, so the index
// we match on (the `match_index`) will go up by one every time we go into a nested abstraction.
// For example: In λ 0 λ 1 λ 2 (so `function_body` = 0 λ 1 λ 2), we'd substitute `replacer`
// into 0, 1, and 2.
// Also note that when we recurse into a nested abstraction, we also must bump up the indicies for
// any free variables in `replacer` by the current depth to accomodate for the fact that those need to point over
// additional lambdas.

// Substitute new copies of the arg into the body.
// Each time the argument is subsituted, a clone of it is allocated and fixed up. Then the leaf
// node being substituted has it's parent repointed to the new argument subtree (with the leaf
// becoming garbage)
// Note that this means if the redex body consists of a single leaf node that gets substituted
// (so it's parent node is the redex abs), then redex.abs gets repointed and the body is garbage now
// Hence, to help with this, the return value of this method is the location of the redex.abs's body,
// (which is either a newly allocated arg subtree or the existing body)
fn substitute_and_fix_body_mut(root: &mut FlatRoot, redex: RedexMut) -> TermIndex {
    struct Context {
        // TermIndex for the redex argument.
        redex_arg: TermIndex,
        // Recomputed usage values. The i-th entry in this vector corresponds to the abstraction at
        // depth i.
        running_usages: Vec<usize>,
        // Usage of redex body
        usage: usize,
        // Current substitution index. This gets incremented every time a substiution happens
        // and is used to perform optimizations where we avoid allocating the last substitution
        // and just reuse the allocation at redex_arg.
        substitution_i: usize,
    }

    impl Context {
        fn new(redex: RedexMut) -> Context {
            Context {
                redex_arg: redex.arg,
                running_usages: vec![],
                usage: redex.usage,
                substitution_i: 0,
            }
        }

        // Current depth. This is 0-indexed.
        fn depth(&self) -> usize {
            self.running_usages.len()
        }
    }

    // Return values:
    // bool - if true, then this method performed a substitution. If `term` is an abstraction, it's
    // usage may now be stale.
    // Option<TermIndex> - if Some(new_arg), then this method performed an allocation and repointed
    // term.parent to point to new_arg. This means that the term's parent's old indicies are now pointing
    // to garbage. This is important when returning from an Abstraction call, as compute_usage_flat needs
    // to use the new pointer.
    fn _substitute_mut(
        ctx: &mut Context,
        root: &mut FlatRoot,
        term: TermWithParent,
    ) -> (bool, Option<TermIndex>) {
        match root[term.term] {
            DebruijnNode::Index(debruijn_index) => {
                // Note that the depth here is 0-indexed, while debruijn_index is 1-indexed
                // Hence need to add one to compare properly. (eg: at depth-0, which is to say at
                // the top body layer, a debruijn index of 1 should get substituted.)
                if debruijn_index == ctx.depth() + 1 {
                    // Optimization opportunity: Instead of making `arg` become garbage, instead reuse it and avoid doing one alloc.
                    let last_arg_allocation = ctx.substitution_i == ctx.usage - 1;

                    let new_arg = if !last_arg_allocation {
                        clone_subtree_and_fix_up(root, ctx.redex_arg, ctx.depth())
                    } else {
                        // Bump up free variables by `depth`
                        // Note that normally we would have fixed up the argument by one prior to
                        // calling this method. However, we also fix down the entire body by one after
                        // calling the method. Both of these fixups cancel out, so we still only just
                        // fix up by `depth`
                        up_by_mut(root, ctx.redex_arg, ctx.depth());
                        ctx.redex_arg
                    };

                    repoint_node(root, term.parent, new_arg);
                    ctx.substitution_i += 1;
                    (true, Some(new_arg))
                } else if debruijn_index > ctx.depth() {
                    // Variable is a free variable, but is NOT getting substituted.
                    // Remember that the body of the term is getting dropped out of the abstraction
                    // Because of this, we need to reduce the term_index by one, since there's one
                    // less abstraction to jump over for the index.
                    root[term.term] = DebruijnNode::Index(debruijn_index - 1);
                    (false, None)
                } else {
                    (false, None)
                }
            }
            DebruijnNode::Abstraction { body, usage } => {
                let body = TermWithParent::body(term.term, body);

                ctx.running_usages.push(0);
                let (did_sub_body, new_body) = _substitute_mut(ctx, root, body);
                let _usage = ctx.running_usages.pop().unwrap();

                // Compute usage due to substitution
                if did_sub_body {
                    let body = new_body.unwrap_or(body.term);
                    root[term.term] = DebruijnNode::Abstraction { body, usage };
                }
                (did_sub_body, None)
            }
            DebruijnNode::Application { func, arg } => {
                let func = TermWithParent::func(term.term, func);
                let arg = TermWithParent::arg(term.term, arg);

                let (did_sub_func, _) = _substitute_mut(ctx, root, func);
                let (did_sub_arg, _) = _substitute_mut(ctx, root, arg);
                (did_sub_func || did_sub_arg, None)
            }
        }
    }
    let mut ctx = Context::new(redex);
    _substitute_mut(&mut ctx, root, redex.body);
    assert_eq!(
        ctx.substitution_i, ctx.usage,
        "Expected substitution count to equal usage!"
    );

    let DebruijnNode::Abstraction { body, .. } = root[redex.abs] else {
        unreachable!(
            "expected abstraction, got {:?} at {} in {root:#?}",
            root[redex.abs], redex.abs
        );
    };
    body
}

/// Clone the given subtree and fix up each free variable by up_by. This effectively fuses the
/// up_by and clone steps together for substitute_mut, eliminating a second tree walk.
/// The returned value points to the newly allocated subtree.
fn clone_subtree_and_fix_up(root: &mut FlatRoot, term: TermIndex, up_by: usize) -> TermIndex {
    fn _clone_subtree_and_fix_up(
        root: &mut FlatRoot,
        term: TermIndex,
        up_by: usize,
        depth: DebruijnDepth,
    ) -> TermIndex {
        match root[term] {
            DebruijnNode::Index(index) => {
                let index = if index >= depth { index + up_by } else { index };
                root.alloc_one(Some(DebruijnNode::Index(index)))
            }
            DebruijnNode::Abstraction { body, usage } => {
                let abs = root.alloc_one(None);
                let body = _clone_subtree_and_fix_up(root, body, up_by, depth + 1);
                root[abs] = DebruijnNode::Abstraction { body, usage };
                abs
            }
            DebruijnNode::Application { func, arg } => {
                let app = root.alloc_one(None);
                let func = _clone_subtree_and_fix_up(root, func, up_by, depth);
                let arg = _clone_subtree_and_fix_up(root, arg, up_by, depth);

                root[app] = DebruijnNode::Application { func, arg };
                app
            }
        }
    }

    _clone_subtree_and_fix_up(root, term, up_by, 1)
}

fn up_by_mut(root: &mut FlatRoot, term: TermIndex, up_by: usize) {
    shift_cutoff_mut(root, term, up_by as isize, 1)
}

// ↑ n = n         if n < cutoff
//       n + up_by otherwise
// ↑ λ t = λ (↑ t) where up_by -> up_by and cutoff -> cutoff + 1
// ↑ (t1 t2) = (↑ t1) (↑ t2)

fn down_one_mut(root: &mut FlatRoot, term: TermIndex) {
    shift_cutoff_mut(root, term, -1, 1)
}

/// Shift the indicies for all terms up by an amount. Indicies below the cutoff are not modified
/// This is useful during beta reduction because we need to "drop out" an abstraction.
fn shift_cutoff_mut(root: &mut FlatRoot, term: TermIndex, up_by: isize, depth: DebruijnDepth) {
    match root[term] {
        DebruijnNode::Index(term_index) => {
            // Recall that an index starts at 1, so if cutoff is set to 1, then this branch will always be taken.
            if term_index >= depth {
                let new_index = term_index.checked_add_signed(up_by).unwrap();
                root[term] = DebruijnNode::Index(new_index);
            }
        }
        DebruijnNode::Application { func, arg } => {
            shift_cutoff_mut(root, func, up_by, depth);
            shift_cutoff_mut(root, arg, up_by, depth);
        }
        DebruijnNode::Abstraction { body, .. } => {
            // We add one to the cutoff here because we don't want to modify bound variables
            // For example, if we're at the outer-most lambda, then any Index(1)s in the lambda body
            // are referring to that lambda's bound variable and we don't modify it.
            shift_cutoff_mut(root, body, up_by, depth + 1);
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
    use crate::debruijn::{self, Debruijn};

    fn compile(term: &str) -> FlatRoot {
        FlatRoot::from(&Debruijn::from_str(term).unwrap())
    }

    fn idx(a: usize) -> DebruijnNode {
        DebruijnNode::Index(a)
    }

    fn abs(body: usize, usage: usize) -> DebruijnNode {
        DebruijnNode::Abstraction {
            body: TermIndex(body),
            usage,
        }
    }

    fn app(func: usize, arg: usize) -> DebruijnNode {
        DebruijnNode::Application {
            func: TermIndex(func),
            arg: TermIndex(arg),
        }
    }

    #[test]
    fn flattening_trivial_idx() {
        let original = Debruijn::from("0");
        let actual = FlatRoot::from(&original);
        let expected = FlatRoot::from(vec![DebruijnNode::Index(0)]);
        assert_eq!(actual, expected)
    }

    #[test]
    fn flattening_trivial_abs() {
        let original = Debruijn::from("λ 1");
        let actual = FlatRoot::from(&original);
        let expected = FlatRoot::from(vec![abs(1, 1), idx(1)]);
        assert_eq!(actual, expected)
    }

    #[test]
    fn flattening_trivial_abs_2() {
        let original = Debruijn::from("λ λ 1");
        let actual = FlatRoot::from(&original);
        let expected = FlatRoot::from(vec![abs(1, 0), abs(2, 1), idx(1)]);
        assert_eq!(actual, expected)
    }

    #[test]
    fn flattening_trivial_app() {
        let original = Debruijn::from("1 2");
        let actual = FlatRoot::from(&original);
        let expected = FlatRoot::from(vec![app(1, 2), idx(1), idx(2)]);
        assert_eq!(actual, expected)
    }

    #[test]
    fn flattening_trivial_app_2() {
        let original = Debruijn::from("(1 2) (3 4)");
        let actual = FlatRoot::from(&original);
        let expected = FlatRoot::from(vec![
            app(1, 4), // 0
            app(2, 3), // 1
            idx(1),    // 2
            idx(2),    // 3
            app(5, 6), // 4
            idx(3),    // 5
            idx(4),    // 6
        ]);
        assert_eq!(actual, expected)
    }

    #[test]
    fn round_trip() {
        let original = Debruijn::from("(λ λ λ 3 1 (2 1)) ((λ λ 2) (λ λ λ 3 1 (2 1))) λ λ 2");
        let flat = FlatRoot::from(&original);
        let roundtripped = Debruijn::from(&flat);

        assert_eq!(
            original, roundtripped,
            "Expected {original}, got {roundtripped}",
        );
    }

    #[test]
    fn usage_zero() {
        let mut root = compile("(λ 2) (λ 50)");

        let redex = RedexMut::try_get(&root, TermWithParent::root(&root)).unwrap();
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

        let redex = RedexMut::try_get(&root, TermWithParent::root(&root)).unwrap();
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

        let redex = RedexMut::try_get(&root, TermWithParent::root(&root)).unwrap();
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

        let redex = RedexMut::try_get(&root, TermWithParent::root(&root)).unwrap();
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

        let redex = RedexMut::try_get(&root, TermWithParent::root(&root)).unwrap();
        assert_eq!(redex.usage, 4);

        substitute_arg_into_body_mut(&mut root, redex);

        let expected = compile("100 λ 101 λ 102 λ 103");

        let actual = Debruijn::from(&root);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }
}
