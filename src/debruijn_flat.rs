use core::fmt;
use std::{
    fmt::{Binary, Display},
    ops::{ControlFlow, Index, IndexMut},
    str::FromStr,
};

use crate::debruijn::Debruijn;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FlatRoot {
    pub backing: Vec<DebruijnNode>,
    pub root: TermIndex,
}
impl FlatRoot {
    fn new() -> FlatRoot {
        FlatRoot {
            backing: vec![],
            root: TermIndex {
                index: 0,
                adjust: 0,
            },
        }
    }

    /// Allocate the given term onto the backing vector. If none is passed, then a dummy node is
    /// allocated, which should be modified by the caller. Otherwise, the node is set to the node
    /// in the input `term`.
    /// The return value is the index to the newly allocated node.
    fn alloc_one(&mut self, term: Option<DebruijnNode>) -> TermIndex {
        // If none, then alloc a dummy node, this should be fixed up afterwards
        let term = term.unwrap_or(DebruijnNode::Index(DebruijnIndex::MAX));
        let term_index = TermIndex::new(self.backing.len());
        self.backing.push(term);
        term_index
    }

    pub fn is_bnf(&self) -> bool {
        let result = self.preorder_walk(|root, term, _| {
            if RedexMut::is_redex(root, term.term) {
                ControlFlow::Break(false)
            } else {
                ControlFlow::Continue(())
            }
        });
        result.unwrap_or(true)
    }

    pub fn get_redexes(&self) -> Vec<RedexMut> {
        let mut redexes = vec![];
        self.preorder_walk(|root, term, parent_chain| {
            if let Some(redex) = RedexMut::try_get(root, term, parent_chain.clone()) {
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
                DebruijnNode::Abstraction(abs) => {
                    let new_abs = new_root.alloc_one(None);
                    let body = _clone(old_root, new_root, abs.body);
                    new_root[new_abs] = DebruijnNode::abs(body, abs.usage);
                    new_abs
                }
                DebruijnNode::Application(app) => {
                    let new_app = new_root.alloc_one(None);
                    let func = _clone(old_root, new_root, app.func);
                    let arg = _clone(old_root, new_root, app.arg);
                    new_root[new_app] = DebruijnNode::app(func, arg);
                    new_app
                }
            }
        }

        let mut new_root = FlatRoot::new();
        _clone(self, &mut new_root, self.root);
        new_root
    }

    pub fn check_usage(&self) -> Result<(), (TermIndex, Usage, Usage)> {
        fn _check_usage(root: &FlatRoot, term: TermIndex) -> Result<(), (TermIndex, Usage, Usage)> {
            match root[term] {
                DebruijnNode::Abstraction(abs) => {
                    _check_usage(root, abs.body)?;
                    let expected = compute_usage_flat(root, abs.body(term));
                    let actual = abs.usage;
                    if actual != expected {
                        Err((term, actual, expected))
                    } else {
                        Ok(())
                    }
                }
                DebruijnNode::Index(_) => Ok(()),
                DebruijnNode::Application(app) => {
                    _check_usage(root, app.func)?;
                    _check_usage(root, app.arg)?;
                    Ok(())
                }
            }
        }
        _check_usage(&self, self.root)
    }

    fn get_abs(&self, term: TermIndex) -> Abstraction {
        match self[term] {
            DebruijnNode::Abstraction(abs) => abs,
            _ => panic!(
                "Expected abstraction for term @ {term}, got {:?}",
                self[term]
            ),
        }
    }

    fn get_app(&self, term: TermIndex) -> Application {
        match self[term] {
            DebruijnNode::Application(app) => app,
            _ => panic!(
                "Expected abstraction for term @ {term}, got {:?}",
                self[term]
            ),
        }
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
        &self.backing[index.index]
    }
}

impl IndexMut<TermIndex> for FlatRoot {
    fn index_mut(&mut self, index: TermIndex) -> &mut Self::Output {
        &mut self.backing[index.index]
    }
}

impl From<Vec<DebruijnNode>> for FlatRoot {
    fn from(backing: Vec<DebruijnNode>) -> Self {
        FlatRoot {
            backing,
            root: TermIndex::new(0),
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
                    root[abs] = DebruijnNode::abs(body, usage);
                    abs
                }
                Debruijn::Application { func, arg } => {
                    let app = root.alloc_one(None);
                    let func = flatten(root, func);
                    let arg = flatten(root, arg);
                    root[app] = DebruijnNode::app(func, arg);
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
                DebruijnNode::Abstraction(abs) => Debruijn::Abstraction {
                    body: Box::new(_from(root, abs.body)),
                },
                DebruijnNode::Application(app) => Debruijn::Application {
                    func: Box::new(_from(root, app.func)),
                    arg: Box::new(_from(root, app.arg)),
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
fn compute_usage(body: &Debruijn) -> Usage {
    fn _compute_usage(term: &Debruijn, depth: DebruijnDepth) -> Usage {
        match term {
            Debruijn::Index(index) => (*index == depth) as Usage,
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
fn compute_usage_flat(root: &FlatRoot, body: TermWithParent) -> Usage {
    let mut usage = 0;
    root.preorder_walk_at(body, |root, term, parent_chain| {
        // Because this is the body of an abstraction, we actually are starting at depth 1
        // (so Index(1) refers to the input variable). If we had started at top-level (or had
        // the abstraction itself as input rather than it's body), then this would be 0.
        let depth = parent_chain.len() + 1;
        if let DebruijnNode::Index(index) = root[term.term] {
            if index == depth {
                usage += 1;
            }
        }
        ControlFlow::Continue::<()>(())
    });

    usage
}

// The depth relative to some term. This is used to determine if a variable is free within a term
// If a given Index node has a DebruijnIndex >= DebruijnDepth, then that Index node is a free variable
// with respect to that subtree)
// Zero indicates that there are no abstractions between the two terms, one indicates one abstraction, etc
type DebruijnDepth = usize;

// The index for the DebruijnNode::Index variant. This is an index for the actual lambda term and works
// just like how Debruijn::Index works.
type DebruijnIndex = usize;

// The number of times a variable is used in an abstraction.
type Usage = usize;

/// A pointer to a given DebruijnNode within a FlatRoot
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TermIndex {
    /// An index into the backing vector of a FlatRoot.
    pub index: usize,
    /// An "adjustment" value. All DebruijnNode::Index nodes are implictly increased or decreased by
    /// this amount. Note that this is cumulative.
    adjust: isize,
}
impl TermIndex {
    /// Create a new TermIndex with adjustment zero.
    pub fn new(index: usize) -> Self {
        Self { index, adjust: 0 }
    }
}

impl Display for TermIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.adjust == 0 {
            write!(f, "{}", self.index)
        } else {
            write!(f, "{} (adjust={})", self.index, self.adjust)
        }
    }
}

impl From<usize> for TermIndex {
    fn from(index: usize) -> Self {
        TermIndex { index, adjust: 0 }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TermWithParent {
    pub term: TermIndex,
    parent: Option<Parent>,
}
impl TermWithParent {
    pub fn root(root: &FlatRoot) -> TermWithParent {
        TermWithParent {
            term: root.root,
            parent: None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Abstraction {
    pub body: TermIndex,
    /// Number of times the input argument is used in the body
    /// If this is zero, then when doing argument substitution, the algorithm can just
    /// return the body and throw away the argument!
    /// This value is constant over the lifetime of the Abstraction (this will become not true if
    /// we do "partial" substition where not all usages of the input argument are substituted)
    pub usage: Usage,
}

impl Abstraction {
    pub fn body(&self, abs_index: TermIndex) -> TermWithParent {
        TermWithParent {
            term: self.body,
            parent: Some(Parent::Body(abs_index)),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Application {
    pub func: TermIndex,
    pub arg: TermIndex,
}

impl Application {
    pub fn func(&self, app_index: TermIndex) -> TermWithParent {
        TermWithParent {
            term: self.func,
            parent: Some(Parent::Func(app_index)),
        }
    }

    pub fn arg(&self, app_index: TermIndex) -> TermWithParent {
        TermWithParent {
            term: self.arg,
            parent: Some(Parent::Arg(app_index)),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum DebruijnNode {
    Index(DebruijnIndex),
    Abstraction(Abstraction),
    Application(Application),
}
impl DebruijnNode {
    pub fn abs(body: TermIndex, usage: usize) -> DebruijnNode {
        DebruijnNode::Abstraction(Abstraction { body, usage })
    }

    pub fn app(func: TermIndex, arg: TermIndex) -> DebruijnNode {
        DebruijnNode::Application(Application { func, arg })
    }
}

impl From<Abstraction> for DebruijnNode {
    fn from(abs: Abstraction) -> Self {
        DebruijnNode::Abstraction(abs)
    }
}

impl From<Application> for DebruijnNode {
    fn from(app: Application) -> Self {
        DebruijnNode::Application(app)
    }
}

impl std::fmt::Debug for DebruijnNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Index(index) => write!(f, "idx@{}", *index),
            Self::Abstraction(abs) => write!(f, "abs: body -> {} (usage={})", abs.body, abs.usage),
            Self::Application(app) => write!(f, "app: func -> {}, arg -> {}", app.func, app.arg),
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

// The sequence of outer abstractions a term is contained in.
// Every element of this vector is an abstraction.
pub type ParentAbstractionChain = Vec<TermIndex>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct RedexMut {
    // The entire chain of abstractions for the parent, which will all need to get fixed up during substitution.
    parent_chain: ParentAbstractionChain,
    // Application term for the redex. If the parent for this is none,
    // then the Redex is actually the root (and therefore is pointed to by FlatRoot.root)
    pub app: TermWithParent,
    // The Abstraction containing the body. This must be an Abstraction
    pub abs: TermIndex,
    // The body of the Abstraction. This must be pointed to by `abs`
    body: TermWithParent,
    // The argument of the Application. This must be pointed to by `app.arg`
    pub arg: TermIndex,
    // The usage of the `body`. Provided for convinence
    body_usage: Usage,
}

impl RedexMut {
    pub fn is_redex(root: &FlatRoot, term: TermIndex) -> bool {
        match root[term] {
            DebruijnNode::Application(app) => match root[app.func] {
                DebruijnNode::Abstraction { .. } => true,
                _ => false,
            },
            _ => false,
        }
    }

    pub fn try_get(
        root: &FlatRoot,
        term: TermWithParent,
        parent_chain: ParentAbstractionChain,
    ) -> Option<RedexMut> {
        match root[term.term] {
            DebruijnNode::Application(app) => match root[app.func] {
                DebruijnNode::Abstraction(abs) => {
                    let body = abs.body(app.func);
                    let redex = RedexMut {
                        app: term,
                        abs: app.func,
                        body,
                        arg: app.arg,
                        body_usage: abs.usage,
                        parent_chain,
                    };
                    Some(redex)
                }
                _ => None,
            },
            _ => None,
        }
    }
}

pub fn beta_reduce(root: &mut FlatRoot, redex: RedexMut) {
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

    // Update parent usages. This should happen before the tree is updated as we may end up with
    // arg becoming garbage or modified (it would technically be fine to actually still do that,
    // because the way arg is modified would not affect it's usage counts, but semantically this
    // is easier to reason aboout, so we do it first.)
    update_parent_chain_usage(root, &redex.parent_chain, redex.body_usage, redex.arg);

    let body = substitute_and_shift_fused(root, &redex);

    // Finally, make the parent point to the body, causing `app` and `abs` to be garbage.
    // The app and abs nodes are no longer pointed to by anything, and therefore are now garbage.
    repoint_node(root, redex.app.parent, body);
}

// Updates the usages of the parent chain.
// MEMORY: Modifies in place, does not allocate or make garbage.
fn update_parent_chain_usage(
    root: &mut FlatRoot,
    parent_chain: &ParentAbstractionChain,
    // Number of times body is used
    body_usage: Usage,
    arg: TermIndex,
) {
    // If there are no parents to update (which happens if the redex is the root)
    // or otherwise has no abstractions in it's parent path, then do nothing.
    if parent_chain.is_empty() {
        return;
    }

    let usages_of_page_in_arg = get_usage_by_depth(root, arg, parent_chain);
    for (depth, parent_term) in parent_chain.iter().enumerate() {
        let abs = root.get_abs(*parent_term);

        let usage_of_parent_in_arg = usages_of_page_in_arg[depth];
        let usage_delta: isize = (body_usage as isize - 1) * usage_of_parent_in_arg as isize;
        let usage = abs.usage.checked_add_signed(usage_delta).unwrap();
        root[*parent_term] = DebruijnNode::abs(abs.body, usage)
    }
}

// Computes the usage of the parents in the parent chain in arg.
// For example, Suppose we have λ λ <body> (λ 1 2 2 3 4).
// The argument here is (λ 1 2 2 3 4)
// In the argument, 1 is bound to the abstraction in the argument, while 2, 3, and 4 are all
// free variables relative to arg. In particular, 2 and 3 are explicitly bound outside of the redex,
// while 4 is unbound.
// Let's write this as a classic term:
// λa. λb. <body> (λc. c b b a <unbound>)
// The parent chain for the redex is effectively [a, b]. In arg, the usage of a is one, and the
// usage of b is two, so the returned usage vector is [1, 2]
// Note that the unbound variable is not included (we could talk about it's usage, but since there's
// no abstraction term to bind it to, we will ignore it), and we also ignore the arg-bound term of c
// since that won't get updated.
fn get_usage_by_depth(
    root: &FlatRoot,
    arg: TermIndex,
    parent_chain: &ParentAbstractionChain,
) -> Vec<Usage> {
    fn _get_usage_by_depth(
        root: &FlatRoot,
        term: TermIndex,
        // The usages of the parent chain. This is sorted such that the first element is higher in the tree
        // eg: usages[0] is the root-most element. This is nonempty
        usages: &mut [Usage],
        // Depth relative to root of the argument subtree
        // This indicates whether or not a node is a free or bound variable
        // ex: If depth == 0, then all variables are free
        // If depth == 1, then nodes with DebruijnIndex = 1 are bound, the rest are free
        // If depth == N, then nodes with DebruijnIndex <= N are bound, the rest are free.
        depth_relative_to_arg: DebruijnDepth,
    ) {
        match root[term] {
            DebruijnNode::Index(index) => {
                // We need to account for the fact that we may be inside an abstraction in the argument
                // If we are, we should skip if this is a bound variable.
                let is_bound = index <= depth_relative_to_arg;
                if is_bound {
                    return;
                }

                // We want to transform this into an index into the usages array,
                // which is sorted by parent-chain depth.
                // In other words, we need to convert from a debruijn index to a debruijn level.

                // arg. For example, if we have index = 5 and parent chain = [a, b, c, d, e, f]
                // but are two abstractions deep into the arg
                // (so depth_relative_to_arg = 2), then this points to
                // [a, b, c, d, e, f]
                //           ^------- here!
                // which is level 4 (actual index = 3) into the array.
                // 6 - (5 - 2)

                // SAFETY: subtraction is safe because we just checked that index <= depth_relative_to_arg
                // and return in the case that this happens.
                let index_relative_to_parent = index - depth_relative_to_arg;

                // In the case of an open term - eg: λ (λ 1 1) 99
                // it is possible for an index to actually point to an implict parent which
                // doesn't actually exist in the tree. In this case, we just do nothing.
                if usages.len() < index_relative_to_parent {
                    return;
                }

                // SAFETY: we just checked that usages.len() < index_relative_to_parent, and return
                // in the case that this happens
                let level = usages.len() - index_relative_to_parent;
                usages[level] += 1;
            }
            DebruijnNode::Abstraction(abs) => {
                _get_usage_by_depth(root, abs.body, usages, depth_relative_to_arg + 1)
            }
            DebruijnNode::Application(app) => {
                _get_usage_by_depth(root, app.func, usages, depth_relative_to_arg);
                _get_usage_by_depth(root, app.arg, usages, depth_relative_to_arg);
            }
        }
    }

    let mut usages = vec![0; parent_chain.len()];
    _get_usage_by_depth(root, arg, &mut usages, 0);

    usages
}

/// Repoint the term at `child` so that it is the child of `parent`. This does not affect the
/// existing parent (which means that the child should either be an orphan--eg: has no existing parent
/// or is root).
/// If `parent` is none, then the child is made the root node of `root`.
/// This does NOT recompute the usage of the parent if the parent is an abstraction.
/// MEMORY: Child becomes garbage after repointing.
fn repoint_node(root: &mut FlatRoot, parent: Option<Parent>, child: TermIndex) {
    match parent {
        Some(Parent::Body(parent)) => {
            let abs = root.get_abs(parent);
            root[parent] = DebruijnNode::abs(child, abs.usage)
        }
        Some(Parent::Func(parent)) => {
            let app = root.get_app(parent);
            root[parent] = DebruijnNode::app(child, app.arg);
        }
        Some(Parent::Arg(parent)) => {
            let app = root.get_app(parent);
            root[parent] = DebruijnNode::app(app.func, child)
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
// MEMORY:
// - Upon substitution, the existing index node becomes garbage.
// - Allocates copies of redex.arg
// - Potentially invalidates redex.body (may repoint redex.abs's body in the case that body consists of a single leaf node that gets substituted)
// - Potentially invalidates redex.arg (becomes garbage in the zero usage case, may be altered in non-zero usage case)
// - Potentially alters redex.parent pointer
fn substitute_and_shift_fused(root: &mut FlatRoot, redex: &RedexMut) -> TermIndex {
    if redex.body_usage == 0 {
        // No need to do anything with the argument because it is never used in the body
        // (Since the argument is not used, the entire arg subtree is garbage now.)
        down_one(root, redex.body.term);
        // Fix up the indicies in it to account for the fact that we are still dropping out the abstraction that the body is in.
        redex.body.term
    } else {
        // Otherwise, perform substitution as usual

        // Perform the actual substition on body.
        // This method actually fuses the fixing down/up that needs to happen for the whole body
        // in addition to performing substitutions.
        let mut ctx = {
            Context {
                redex_arg: redex.arg,
                depth: 0,
                usage: redex.body_usage,
                substitution_i: 0,
            }
        };
        _substitute_shift_fused(&mut ctx, root, redex.body);
        assert_eq!(
            ctx.substitution_i, ctx.usage,
            "Expected substitution count to equal usage!"
        );

        // The body of abs may get repointed if the redex body consists of a single leaf node that gets substituted.
        // Hence, we need to check for this and get the actually new body.
        root.get_abs(redex.abs).body
    }
}
struct Context {
    // TermIndex for the redex argument.
    redex_arg: TermIndex,
    // Depth relative to the root
    depth: DebruijnDepth,
    // Usage of redex body
    usage: Usage,
    // Current substitution index. This gets incremented every time a substiution happens
    // and is used to perform optimizations where we avoid allocating the last substitution
    // and just reuse the allocation at redex_arg.
    substitution_i: usize,
}

impl Context {
    fn last_arg_allocation(&self) -> bool {
        self.substitution_i == self.usage - 1
    }
    fn is_substituting(&self, debruijn_index: DebruijnIndex) -> bool {
        // Note that the depth here is 0-indexed, while debruijn_index is 1-indexed
        // Hence need to add one to compare properly. (eg: at depth-0, which is to say at
        // the top body layer, a debruijn index of 1 should get substituted.)
        debruijn_index == self.depth + 1
    }
}

// Return values:
// bool - if true, then this method performed a substitution. If `term` is an abstraction, it's
// usage may now be stale.
// Option<TermIndex> - if Some(new_arg), then this method performed an allocation and repointed
// term.parent to point to new_arg. This means that the term's parent's old indicies are now pointing
// to garbage. This is important when returning from an Abstraction call, as compute_usage_flat needs
// to use the new pointer.
fn _substitute_shift_fused(
    ctx: &mut Context,
    root: &mut FlatRoot,
    term: TermWithParent,
) -> (bool, Option<TermIndex>) {
    match root[term.term] {
        DebruijnNode::Index(debruijn_index) => {
            if ctx.is_substituting(debruijn_index) {
                let new_arg = if ctx.last_arg_allocation() {
                    // Optimization opportunity: Instead of making `arg` become garbage, instead reuse it and avoid doing one alloc.
                    // Bump up free variables by `depth`
                    // Note that normally we would have fixed up the argument by one prior to
                    // calling this method. However, we also fix down the entire body by one after
                    // calling the method. Both of these fixups cancel out, so we still only just
                    // fix up by `depth`
                    up_by(root, ctx.redex_arg, ctx.depth);
                    ctx.redex_arg
                } else {
                    clone_subtree_and_fix_up_fused(root, ctx.redex_arg, ctx.depth)
                };

                repoint_node(root, term.parent, new_arg);
                ctx.substitution_i += 1;
                (true, Some(new_arg))
            } else if debruijn_index > ctx.depth {
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
        DebruijnNode::Abstraction(mut abs) => {
            let body = abs.body(term.term);
            ctx.depth += 1;
            let (did_sub_body, new_body) = _substitute_shift_fused(ctx, root, body);
            ctx.depth -= 1;

            // If the body consists of a single leaf node, then the body will now point elsewhere.
            // If this is the case, we need to re-point abs to the new body.
            if did_sub_body && let Some(new_body) = new_body {
                abs.body = new_body;
                root[term.term] = abs.into();
            }
            (did_sub_body, None)
        }
        DebruijnNode::Application(app) => {
            let func = app.func(term.term);
            let arg = app.arg(term.term);

            let (did_sub_func, _) = _substitute_shift_fused(ctx, root, func);
            let (did_sub_arg, _) = _substitute_shift_fused(ctx, root, arg);
            (did_sub_func || did_sub_arg, None)
        }
    }
}

/// Clone the given subtree and fix up each free variable by up_by. This effectively fuses the
/// up_by and clone steps together for substitution, eliminating a second tree walk.
///
/// MEMORY: Allocates new subtree, returned value is the newly allocated tree
fn clone_subtree_and_fix_up_fused(
    root: &mut FlatRoot,
    term: TermIndex,
    up_by: DebruijnDepth,
) -> TermIndex {
    fn _clone_subtree_and_fix_up_fused(
        root: &mut FlatRoot,
        term: TermIndex,
        up_by: DebruijnDepth,
        depth: DebruijnDepth,
    ) -> TermIndex {
        match root[term] {
            DebruijnNode::Index(index) => {
                let is_free = index >= depth;
                let index = if is_free { index + up_by } else { index };
                root.alloc_one(Some(DebruijnNode::Index(index)))
            }
            DebruijnNode::Abstraction(abs) => {
                let new_abs = root.alloc_one(None);
                let body = _clone_subtree_and_fix_up_fused(root, abs.body, up_by, depth + 1);
                root[new_abs] = DebruijnNode::abs(body, abs.usage);
                new_abs
            }
            DebruijnNode::Application(app) => {
                let new_app = root.alloc_one(None);
                let func = _clone_subtree_and_fix_up_fused(root, app.func, up_by, depth);
                let arg = _clone_subtree_and_fix_up_fused(root, app.arg, up_by, depth);

                root[new_app] = DebruijnNode::app(func, arg);
                new_app
            }
        }
    }

    _clone_subtree_and_fix_up_fused(root, term, up_by, 1)
}

/// MEMORY: Modifies in place, does not allocate or create garbage.
fn up_by(root: &mut FlatRoot, term: TermIndex, up_by: DebruijnDepth) {
    shift_cutoff(root, term, up_by as isize, 1)
}

// ↑ n = n         if n < cutoff
//       n + up_by otherwise
// ↑ λ t = λ (↑ t) where up_by -> up_by and cutoff -> cutoff + 1
// ↑ (t1 t2) = (↑ t1) (↑ t2)

/// MEMORY: Modifies in place, does not allocate or create garbage.
fn down_one(root: &mut FlatRoot, term: TermIndex) {
    shift_cutoff(root, term, -1, 1)
}

/// Shift the indicies for all terms up by an amount. Indicies below the cutoff are not modified
/// This is useful during beta reduction because we need to "drop out" an abstraction.
///
/// MEMORY: Modifies in place, does not allocate or create garbage.
fn shift_cutoff(root: &mut FlatRoot, term: TermIndex, up_by: isize, depth: DebruijnDepth) {
    match root[term] {
        DebruijnNode::Index(term_index) => {
            // Recall that an index starts at 1, so if depth is set to 1, then this branch will always be taken.
            let is_free = term_index >= depth;
            if is_free {
                let new_index = term_index.checked_add_signed(up_by).unwrap();
                root[term] = DebruijnNode::Index(new_index);
            }
        }
        DebruijnNode::Application(app) => {
            shift_cutoff(root, app.func, up_by, depth);
            shift_cutoff(root, app.arg, up_by, depth);
        }
        DebruijnNode::Abstraction(abs) => {
            // We add one to the cutoff here because we don't want to modify bound variables
            // For example, if we're at the outer-most lambda, then any Index(1)s in the lambda body
            // are referring to that lambda's bound variable and we don't modify it.
            shift_cutoff(root, abs.body, up_by, depth + 1);
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
        FlatRoot::from(&Debruijn::from_str(term).unwrap())
    }

    fn idx(a: DebruijnIndex) -> DebruijnNode {
        DebruijnNode::Index(a)
    }

    fn abs(body: impl Into<TermIndex>, usage: Usage) -> DebruijnNode {
        DebruijnNode::abs(body.into(), usage)
    }

    fn app(func: impl Into<TermIndex>, arg: impl Into<TermIndex>) -> DebruijnNode {
        DebruijnNode::app(func.into(), arg.into())
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

        let redex = RedexMut::try_get(&root, TermWithParent::root(&root), vec![]).unwrap();
        assert_eq!(redex.body_usage, 0);

        beta_reduce(&mut root, redex);

        let expected = compile("1");

        let actual = Debruijn::from(&root);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }

    #[test]
    fn usage_one() {
        let mut root = compile("(λ 1) (λ 50)");

        let redex = RedexMut::try_get(&root, TermWithParent::root(&root), vec![]).unwrap();
        assert_eq!(redex.body_usage, 1);

        beta_reduce(&mut root, redex);

        let expected = compile("λ 50");

        let actual = Debruijn::from(&root);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }

    #[test]
    fn body_is_leaf() {
        let mut root = compile("(λ 1) (1 2 3 4)");

        let redex = RedexMut::try_get(&root, TermWithParent::root(&root), vec![]).unwrap();
        assert_eq!(redex.body_usage, 1);

        beta_reduce(&mut root, redex);

        let expected = compile("1 2 3 4");

        let actual = Debruijn::from(&root);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }

    #[test]
    fn body_is_not_leaf() {
        let mut root = compile("(λ λ 2) (1 2 3 4)");

        let redex = RedexMut::try_get(&root, TermWithParent::root(&root), vec![]).unwrap();
        assert_eq!(redex.body_usage, 1);

        beta_reduce(&mut root, redex);

        let expected = compile("λ 2 3 4 5");

        let actual = Debruijn::from(&root);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }

    #[test]
    fn usage_many() {
        let mut root = compile("(λ 1 λ 2 λ 3 λ 4) 100");

        let redex = RedexMut::try_get(&root, TermWithParent::root(&root), vec![]).unwrap();
        assert_eq!(redex.body_usage, 4);

        beta_reduce(&mut root, redex);

        let expected = compile("100 λ 101 λ 102 λ 103");

        let actual = Debruijn::from(&root);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }
}
