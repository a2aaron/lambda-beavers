use core::fmt;
use std::{
    fmt::{Binary, Display},
    ops::{ControlFlow, Index, IndexMut},
    str::FromStr,
};

use crate::{
    debruijn::Debruijn,
    treewalk::{ActionCtx, ChildResults},
};

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
                subterm_adjust: None,
            },
        }
    }

    /// Allocate the given term onto the backing vector. The node is set to the node
    /// in the input `term`.
    /// The return value is the index to the newly allocated node.
    fn alloc(&mut self, term: DebruijnNode) -> TermIndex {
        let term_index = TermIndex::new(self.backing.len());
        self.backing.push(term);
        term_index
    }

    pub fn is_bnf(&self) -> bool {
        let result = self.preorder_walk(|root, ctx| {
            if RedexMut::is_redex(root, ctx.term.term) {
                ControlFlow::Break(false)
            } else {
                ControlFlow::Continue(())
            }
        });
        result.unwrap_or(true)
    }

    pub fn get_redexes(&self) -> Vec<RedexMut> {
        let mut redexes = vec![];
        self.preorder_walk(|root, ctx| {
            if let Some(redex) = RedexMut::try_get(root, ctx) {
                redexes.push(redex);
            }
            ControlFlow::Continue::<()>(())
        });
        redexes
    }

    pub fn normalized(&self) -> FlatRoot {
        let mut new_root = FlatRoot::new();
        let root_node = self.postorder_walk(|_root, _ctx, result| match result {
            ChildResults::Index(idx) => new_root.alloc(DebruijnNode::Index(idx)),
            ChildResults::Abstraction { abs, body_result } => {
                new_root.alloc(DebruijnNode::abs(body_result, abs.usage))
            }
            ChildResults::Application {
                func_result,
                arg_result,
                ..
            } => new_root.alloc(DebruijnNode::app(func_result, arg_result)),
        });
        new_root.root = root_node;
        new_root
    }

    pub fn check_usage(&self) -> Result<(), (TermIndex, Usage, Usage)> {
        let result = self.preorder_walk(|root, ctx| {
            if let DebruijnNode::Abstraction(abs) = root[ctx.term] {
                let expected = compute_usage_flat(root, ctx);
                let actual = abs.usage;
                if actual != expected {
                    return ControlFlow::Break((ctx.term.term, actual, expected));
                }
            };
            ControlFlow::Continue(())
        });
        match result {
            Some(bad) => Err(bad),
            None => Ok(()),
        }
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

impl Index<TermWithParent> for FlatRoot {
    type Output = DebruijnNode;

    fn index(&self, index: TermWithParent) -> &Self::Output {
        &self[index.term]
    }
}

impl IndexMut<TermWithParent> for FlatRoot {
    fn index_mut(&mut self, index: TermWithParent) -> &mut Self::Output {
        &mut self[index.term]
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
                Debruijn::Index(index) => root.alloc(DebruijnNode::idx(*index)),
                Debruijn::Abstraction { body } => {
                    let usage = compute_usage(&body);
                    let body = flatten(root, body);
                    root.alloc(DebruijnNode::abs(body, usage))
                }
                Debruijn::Application { func, arg } => {
                    let func = flatten(root, func);
                    let arg = flatten(root, arg);
                    root.alloc(DebruijnNode::app(func, arg))
                }
            }
        }

        let mut root = FlatRoot::new();
        root.root = flatten(&mut root, term);
        root
    }
}

impl From<&FlatRoot> for Debruijn {
    fn from(root: &FlatRoot) -> Self {
        root.postorder_walk(|_root, ctx, child_results| match child_results {
            ChildResults::Index(idx) => Debruijn::Index(idx.get(ctx.chain)),
            ChildResults::Abstraction { body_result, .. } => Debruijn::Abstraction {
                body: Box::new(body_result),
            },
            ChildResults::Application {
                func_result,
                arg_result,
                ..
            } => Debruijn::Application {
                func: Box::new(func_result),
                arg: Box::new(arg_result),
            },
        })
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
/// eg: in λ 1 λ 2 λ 3, we have that 1, 2, and 3 all refer to the same variable, so the usage is 3
/// Note that ctx needs to be pointing at an abstraction!
fn compute_usage_flat(root: &FlatRoot, ctx: &mut ActionCtx) -> Usage {
    let mut usage = 0;
    let init_depth = ctx.chain.debruijn_depth();
    root.preorder_walk_at(ctx, |root, ctx| {
        if let DebruijnNode::Index(index) = root[ctx.term] {
            let depth_relative_to_arg = ctx.chain.debruijn_depth() - init_depth;
            if index.get(ctx.chain) == depth_relative_to_arg {
                usage += 1;
            }
        }
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
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct DebruijnIndex(usize);

impl DebruijnIndex {
    pub fn get(&self, chain: &ParentChain) -> usize {
        self.0
    }

    pub fn get_raw(&self) -> usize {
        self.0
    }
}

// The number of times a variable is used in an abstraction.
type Usage = usize;

/// A pointer to a given DebruijnNode within a FlatRoot
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TermIndex {
    /// An index into the backing vector of a FlatRoot.
    pub index: usize,
    /// An "adjustment" value. All DebruijnNode::Index nodes are implictly increased or decreased by
    /// this amount. Note that this is cumulative.
    pub subterm_adjust: Option<isize>,
}
impl TermIndex {
    /// Create a new TermIndex with adjustment zero.
    pub fn new(index: usize) -> Self {
        Self {
            index,
            subterm_adjust: None,
        }
    }
}

impl Display for TermIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(adjust) = self.subterm_adjust {
            write!(f, "{} (adjust={})", self.index, adjust)
        } else {
            write!(f, "{}", self.index)
        }
    }
}

impl From<usize> for TermIndex {
    fn from(index: usize) -> Self {
        TermIndex {
            index,
            subterm_adjust: None,
        }
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
    pub fn idx(index: usize) -> DebruijnNode {
        DebruijnNode::Index(DebruijnIndex(index))
    }

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
            Self::Index(index) => write!(f, "idx@{}", index.get_raw()),
            Self::Abstraction(abs) => write!(f, "abs: body -> {} (usage={})", abs.body, abs.usage),
            Self::Application(app) => write!(f, "app: func -> {}, arg -> {}", app.func, app.arg),
        }
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
#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct ParentChain {
    pub abstractions: Vec<TermIndex>,
    full_chain: Vec<TermIndex>,
}

impl ParentChain {
    pub fn new() -> ParentChain {
        ParentChain::default()
    }
    pub fn push_abs(&mut self, index: TermIndex, _abs: Abstraction) {
        self.abstractions.push(index);
        self.full_chain.push(index);
    }
    pub fn pop_abs(&mut self, _abs: Abstraction) {
        self.abstractions.pop();
        self.full_chain.pop();
    }

    pub fn push_app(&mut self, index: TermIndex, _app: Application) {
        self.full_chain.push(index);
    }

    pub fn pop_app(&mut self, _app: Application) {
        self.full_chain.pop();
    }

    pub fn debruijn_depth(&self) -> DebruijnDepth {
        self.abstractions.len()
    }

    fn iter_abs(&self) -> std::slice::Iter<'_, TermIndex> {
        self.abstractions.iter()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct RedexMut {
    // The entire chain of abstractions for the parent, which will all need to get fixed up during substitution.
    parent_chain: ParentChain,
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

    pub fn try_get(root: &FlatRoot, ctx: &mut ActionCtx) -> Option<RedexMut> {
        match root[ctx.term] {
            DebruijnNode::Application(app) => match root[app.func] {
                DebruijnNode::Abstraction(abs) => {
                    let body = abs.body(app.func);
                    let redex = RedexMut {
                        app: ctx.term,
                        abs: app.func,
                        body,
                        arg: app.arg,
                        body_usage: abs.usage,
                        parent_chain: ctx.chain.clone(),
                    };
                    Some(redex)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn arg(&self) -> TermWithParent {
        TermWithParent {
            term: self.arg,
            parent: Some(Parent::Arg(self.app.term)),
        }
    }

    fn arg_ctx(&'_ mut self) -> ActionCtx<'_> {
        ActionCtx {
            term: self.arg(),
            chain: &mut self.parent_chain,
        }
    }

    fn body_ctx(&'_ mut self) -> ActionCtx<'_> {
        ActionCtx {
            term: self.body,
            chain: &mut self.parent_chain,
        }
    }
}

pub fn beta_reduce(root: &mut FlatRoot, mut redex: RedexMut) {
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
    let body_usage = redex.body_usage;
    let mut ctx = redex.arg_ctx();
    update_parent_chain_usage(root, &mut ctx, body_usage);

    let body = substitute_and_shift_fused(root, &mut redex);

    // Finally, make the parent point to the body, causing `app` and `abs` to be garbage.
    // The app and abs nodes are no longer pointed to by anything, and therefore are now garbage.
    repoint_node(root, redex.app.parent, body);
}

// Updates the usages of the parent chain.
// MEMORY: Modifies in place, does not allocate or make garbage.
fn update_parent_chain_usage(
    root: &mut FlatRoot,
    ctx: &mut ActionCtx,
    // Number of times body is used
    body_usage: Usage,
) {
    // If there are no parents to update (which happens if the redex is the root)
    // or otherwise has no abstractions in it's parent path, then do nothing.
    if ctx.chain.debruijn_depth() == 0 {
        return;
    }

    let usages_of_page_in_arg = get_usage_by_depth(root, ctx);
    for (depth, parent_term) in ctx.chain.iter_abs().enumerate() {
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
fn get_usage_by_depth(root: &FlatRoot, ctx: &mut ActionCtx) -> Vec<Usage> {
    let init_depth = ctx.chain.debruijn_depth();
    let mut usages = vec![0; init_depth];
    root.preorder_walk_at(ctx, |root, ctx| {
        if let DebruijnNode::Index(index) = root[ctx.term] {
            let depth_relative_to_arg = ctx.chain.debruijn_depth() - init_depth;
            // We need to account for the fact that we may be inside an abstraction in the argument
            // If we are, we should skip if this is a bound variable.
            let is_bound = index.get(ctx.chain) <= depth_relative_to_arg;
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
            let index_relative_to_parent = index.get(ctx.chain) - depth_relative_to_arg;

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
    });
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
fn substitute_and_shift_fused(root: &mut FlatRoot, redex: &mut RedexMut) -> TermIndex {
    if redex.body_usage == 0 {
        // No need to do anything with the argument because it is never used in the body
        // (Since the argument is not used, the entire arg subtree is garbage now.)
        down_one(root, &mut redex.body_ctx());
        // Fix up the indicies in it to account for the fact that we are still dropping out the abstraction that the body is in.
        redex.body.term
    } else {
        // Otherwise, perform substitution as usual

        // Perform the actual substition on body.
        // This method actually fuses the fixing down/up that needs to happen for the whole body
        // in addition to performing substitutions.
        substitute_shift_fused_nonzero_usage(root, redex);

        // The body of abs may get repointed if the redex body consists of a single leaf node that gets substituted.
        // Hence, we need to check for this and get the actually new body.
        root.get_abs(redex.abs).body
    }
}

fn substitute_shift_fused_nonzero_usage(root: &mut FlatRoot, redex: &mut RedexMut) {
    let mut substitution_i = 0;
    let init_depth = redex.parent_chain.debruijn_depth();

    let mut redex2 = redex.clone();
    let arg_ctx = &mut redex2.arg_ctx();
    let redex_arg = redex.arg;
    let body_usage = redex.body_usage;
    root.preorder_walk_at_mut(&mut redex.body_ctx(), |root, ctx| {
        let term = ctx.term;
        let chain = &ctx.chain;
        if let DebruijnNode::Index(debruijn_index) = root[term] {
            let depth_relative_to_arg = chain.debruijn_depth() - init_depth;
            // Note that the depth here is 0-indexed, while debruijn_index is 1-indexed
            // Hence need to add one to compare properly. (eg: at depth-0, which is to say at
            // the top body layer, a debruijn index of 1 should get substituted.)
            let is_substituting = debruijn_index.get(chain) == depth_relative_to_arg + 1;
            if is_substituting {
                let last_arg_allocation = substitution_i == body_usage - 1;
                let new_arg = if last_arg_allocation {
                    // Optimization opportunity: Instead of making `arg` become garbage, instead reuse it and avoid doing one alloc.
                    // Bump up free variables by `depth`
                    // Note that normally we would have fixed up the argument by one prior to
                    // calling this method. However, we also fix down the entire body by one after
                    // calling the method. Both of these fixups cancel out, so we still only just
                    // fix up by `depth`
                    up_by(root, arg_ctx, depth_relative_to_arg);
                    redex_arg
                } else {
                    clone_subtree_and_fix_up_fused(root, arg_ctx, depth_relative_to_arg)
                };

                repoint_node(root, term.parent, new_arg);
                substitution_i += 1;
            } else if debruijn_index.get(chain) > depth_relative_to_arg {
                // Variable is a free variable, but is NOT getting substituted.
                // Remember that the body of the term is getting dropped out of the abstraction
                // Because of this, we need to reduce the term_index by one, since there's one
                // less abstraction to jump over for the index.
                root[term] = DebruijnNode::idx(debruijn_index.get(chain) - 1);
            }
        }
    });
    assert_eq!(
        substitution_i, redex.body_usage,
        "Expected substitution count to equal usage!"
    );
}

/// Clone the given subtree and fix up each free variable by up_by. This effectively fuses the
/// up_by and clone steps together for substitution, eliminating a second tree walk.
///
/// MEMORY: Allocates new subtree, returned value is the newly allocated tree
fn clone_subtree_and_fix_up_fused(
    root: &mut FlatRoot,
    ctx: &mut ActionCtx,
    up_by: DebruijnDepth,
) -> TermIndex {
    let init_depth = ctx.chain.debruijn_depth();
    root.postorder_walk_at_mut(ctx, |root, ctx, result| {
        let chain = &ctx.chain;
        match result {
            ChildResults::Index(index) => {
                let depth_relative_to_term = chain.debruijn_depth() + 1 - init_depth;
                let is_free = index.get(chain) >= depth_relative_to_term;
                let index = if is_free {
                    index.get(chain) + up_by
                } else {
                    index.get(chain)
                };
                root.alloc(DebruijnNode::idx(index))
            }
            ChildResults::Abstraction { abs, body_result } => {
                root.alloc(DebruijnNode::abs(body_result, abs.usage))
            }
            ChildResults::Application {
                func_result,
                arg_result,
                ..
            } => root.alloc(DebruijnNode::app(func_result, arg_result)),
        }
    })
}

/// MEMORY: Modifies in place, does not allocate or create garbage.
fn up_by(root: &mut FlatRoot, ctx: &mut ActionCtx, up_by: DebruijnDepth) {
    shift_cutoff(root, ctx, up_by as isize, 1)
}

// ↑ n = n         if n < cutoff
//       n + up_by otherwise
// ↑ λ t = λ (↑ t) where up_by -> up_by and cutoff -> cutoff + 1
// ↑ (t1 t2) = (↑ t1) (↑ t2)

/// MEMORY: Modifies in place, does not allocate or create garbage.
fn down_one(root: &mut FlatRoot, ctx: &mut ActionCtx) {
    shift_cutoff(root, ctx, -1, 1)
}

/// Shift the indicies for all terms up by an amount. Indicies below the cutoff are not modified
/// This is useful during beta reduction because we need to "drop out" an abstraction.
///
/// MEMORY: Modifies in place, does not allocate or create garbage.
fn shift_cutoff(root: &mut FlatRoot, ctx: &mut ActionCtx, up_by: isize, depth: DebruijnDepth) {
    let init_depth = ctx.chain.debruijn_depth();
    root.preorder_walk_at_mut(ctx, |root, ctx| {
        let term = ctx.term.term;
        let chain = &ctx.chain;
        if let DebruijnNode::Index(term_index) = root[term] {
            let depth_relative_to_term = chain.debruijn_depth() + depth - init_depth;
            // Recall that an index starts at 1, so if depth is set to 1, then this branch will always be taken.
            let is_free = term_index.get(chain) >= depth_relative_to_term;
            if is_free {
                let new_index = term_index.get(chain).checked_add_signed(up_by).unwrap();
                root[term] = DebruijnNode::idx(new_index);
            }
        };
    });
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

    fn redex_from_root(root: &FlatRoot) -> RedexMut {
        let mut ctx = ActionCtx {
            term: TermWithParent::root(root),
            chain: &mut ParentChain::new(),
        };
        RedexMut::try_get(root, &mut ctx).unwrap()
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
    fn round_trip_normalized() {
        let original = Debruijn::from("(((λ (λ ((2 1) 2))) (λ (λ 2))) (λ (λ 1)))");
        let original2 = Debruijn::from("(λ λ 2 1 2) (λ λ 2) λ λ 1");
        assert_eq!(original, original2);
        let flat = FlatRoot::from(&original).normalized();
        let roundtripped = Debruijn::from(&flat);

        assert_eq!(
            original, roundtripped,
            "Expected {original}, got {roundtripped}",
        );
    }

    #[test]
    fn usage_zero() {
        let mut root = compile("(λ 2) (λ 50)");

        let redex = redex_from_root(&root);
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

        let redex = redex_from_root(&root);
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

        let redex = redex_from_root(&root);
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

        let redex = redex_from_root(&root);
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

        let redex = redex_from_root(&root);
        assert_eq!(redex.body_usage, 4);

        beta_reduce(&mut root, redex);

        let expected = compile("100 λ 101 λ 102 λ 103");

        let actual = Debruijn::from(&root);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }
}
