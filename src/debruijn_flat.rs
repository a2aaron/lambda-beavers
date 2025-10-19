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
    pub root: DebruijnEdge,
}
impl FlatRoot {
    fn new() -> FlatRoot {
        FlatRoot {
            backing: vec![],
            root: DebruijnEdge {
                child: 0,
                adjust: None,
            },
        }
    }

    /// Allocate the given term onto the backing vector. The node is set to the node
    /// in the input `term`.
    /// The return value is the index to the newly allocated node.
    fn alloc(&mut self, term: DebruijnNode) -> DebruijnEdge {
        let term_index = DebruijnEdge::new(self.backing.len());
        self.backing.push(term);
        term_index
    }

    pub fn is_bnf(&self) -> bool {
        let result = self.preorder_walk(|root, ctx| {
            if RedexMut::is_redex(root, ctx.term.child) {
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
        let root_node = self.postorder_walk(|_root, ctx, result| match result {
            ChildResults::Index(idx) => {
                let index = idx.get(ctx.chain);
                new_root.alloc(DebruijnNode::idx(index))
            }
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

    pub fn check_usage(&self) -> Result<(), (BackingIndex, Usage, Usage)> {
        let result = self.preorder_walk(|root, ctx| {
            if let DebruijnNode::Abstraction(abs) = root[ctx.term] {
                let expected = compute_usage_flat(root, ctx);
                let actual = abs.usage;
                if actual != expected {
                    return ControlFlow::Break((ctx.term.child, actual, expected));
                }
            };
            ControlFlow::Continue(())
        });
        match result {
            Some(bad) => Err(bad),
            None => Ok(()),
        }
    }

    fn get_abs(&self, term: BackingIndex) -> Abstraction {
        match self[term] {
            DebruijnNode::Abstraction(abs) => abs,
            _ => panic!(
                "Expected abstraction for term @ {term}, got {:?}",
                self[term]
            ),
        }
    }

    fn get_app(&self, term: BackingIndex) -> Application {
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

impl Index<BackingIndex> for FlatRoot {
    type Output = DebruijnNode;

    fn index(&self, index: BackingIndex) -> &Self::Output {
        &self.backing[index]
    }
}

impl IndexMut<BackingIndex> for FlatRoot {
    fn index_mut(&mut self, index: BackingIndex) -> &mut Self::Output {
        &mut self.backing[index]
    }
}

impl Index<DebruijnEdge> for FlatRoot {
    type Output = DebruijnNode;

    fn index(&self, index: DebruijnEdge) -> &Self::Output {
        &self[index.child]
    }
}

impl IndexMut<DebruijnEdge> for FlatRoot {
    fn index_mut(&mut self, index: DebruijnEdge) -> &mut Self::Output {
        &mut self[index.child]
    }
}

impl Index<DoubleEndedEdge> for FlatRoot {
    type Output = DebruijnNode;

    fn index(&self, index: DoubleEndedEdge) -> &Self::Output {
        &self[index.child]
    }
}

impl IndexMut<DoubleEndedEdge> for FlatRoot {
    fn index_mut(&mut self, index: DoubleEndedEdge) -> &mut Self::Output {
        &mut self[index.child]
    }
}

impl From<Vec<DebruijnNode>> for FlatRoot {
    fn from(backing: Vec<DebruijnNode>) -> Self {
        FlatRoot {
            backing,
            root: DebruijnEdge::new(0),
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
        fn flatten(root: &mut FlatRoot, term: &Debruijn) -> DebruijnEdge {
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
pub fn compute_usage_flat(root: &FlatRoot, ctx: &mut ActionCtx) -> Usage {
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DebruijnIndex(usize);

impl DebruijnIndex {
    pub fn get(&self, chain: &ParentChain) -> usize {
        let adjustment = chain.total_adjust(self.0);
        let final_index = self.0.checked_add_signed(adjustment).unwrap();
        final_index
    }

    pub fn get_raw(&self) -> usize {
        self.0
    }
}

// The number of times a variable is used in an abstraction.
pub type Usage = usize;
/// A pointer to a given DebruijnNode within a FlatRoot
pub type BackingIndex = usize;
pub type Adjustment = Option<isize>;

/// An edge in the debruijn tree. This specific consists of
/// - The child node
/// - The adjustment, which is attached to the edge itself
/// ```
///   | adjust
///   V
/// child
/// ```
/// It does not contain the parent index, use EdgeWithParent for that.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DebruijnEdge {
    /// An index into the backing vector of a FlatRoot.
    pub child: BackingIndex,
    /// An "adjustment" value. All DebruijnNode::Index nodes are implictly increased or decreased by
    /// this amount. Note that this is cumulative.
    pub adjust: Adjustment,
}
impl DebruijnEdge {
    /// Create a new TermIndex with adjustment zero.
    pub fn new(child: BackingIndex) -> Self {
        Self {
            child,
            adjust: None,
        }
    }
}

impl Display for DebruijnEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(adjust) = self.adjust {
            write!(f, "{} (adjust={})", self.child, adjust)
        } else {
            write!(f, "{}", self.child)
        }
    }
}

impl From<BackingIndex> for DebruijnEdge {
    fn from(index: BackingIndex) -> Self {
        DebruijnEdge {
            child: index,
            adjust: None,
        }
    }
}

/// An edge in the Debruijn tree, containing:
/// - The parent node (if there is one. for the root, there is no parent)
/// - The type of parent-edge this edge is (ie: is this an edge from an abstraction to body,
/// from application to arg, application to func, or into-root)
/// It does not contain the child edge
/// ```
/// parent (if present)
///    | edge type
///    V
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeWithParent {
    /// The "edge" has no parent, and the child here is the root of the tree
    IntoRoot,
    /// The edge is an abstraction to body edge, and the BackingIndex here is the index for the abstraction
    AbsToBody(BackingIndex),
    /// The edge is an application to function edge, and the BackingIndex here is the index for the application
    AppToFunc(BackingIndex),
    /// The edge is an application to argument edge, and the BackingIndex here is the index for the application
    AppToArg(BackingIndex),
}
impl EdgeWithParent {
    fn backing_index(&self) -> Option<BackingIndex> {
        match self {
            EdgeWithParent::IntoRoot => None,
            EdgeWithParent::AbsToBody(abs) => Some(*abs),
            EdgeWithParent::AppToFunc(app) => Some(*app),
            EdgeWithParent::AppToArg(app) => Some(*app),
        }
    }
}

/// Struct containing an edge along with the parent and child
/// parent      <- edge_w_parent backing index (if present)
///   | adjust
/// child      
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DoubleEndedEdge {
    pub edge_w_parent: EdgeWithParent,
    pub child: BackingIndex,
    pub adjust: Adjustment,
}
impl DoubleEndedEdge {
    pub fn root(root: &FlatRoot) -> DoubleEndedEdge {
        DoubleEndedEdge {
            edge_w_parent: EdgeWithParent::IntoRoot,
            child: root.root.child,
            adjust: None,
        }
    }

    pub fn parent_index(&self) -> Option<BackingIndex> {
        self.edge_w_parent.backing_index()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Abstraction {
    pub body: DebruijnEdge,
    /// Number of times the input argument is used in the body
    /// If this is zero, then when doing argument substitution, the algorithm can just
    /// return the body and throw away the argument!
    /// This value is constant over the lifetime of the Abstraction (this will become not true if
    /// we do "partial" substition where not all usages of the input argument are substituted)
    pub usage: Usage,
}

impl Abstraction {
    pub fn body(&self, abs_index: BackingIndex) -> DoubleEndedEdge {
        DoubleEndedEdge {
            child: self.body.child,
            adjust: self.body.adjust,
            edge_w_parent: EdgeWithParent::AbsToBody(abs_index),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Application {
    pub func: DebruijnEdge,
    pub arg: DebruijnEdge,
}

impl Application {
    pub fn func(&self, app_index: BackingIndex) -> DoubleEndedEdge {
        DoubleEndedEdge {
            child: self.func.child,
            adjust: self.func.adjust,
            edge_w_parent: EdgeWithParent::AppToFunc(app_index),
        }
    }

    pub fn arg(&self, app_index: BackingIndex) -> DoubleEndedEdge {
        DoubleEndedEdge {
            child: self.arg.child,
            adjust: self.arg.adjust,
            edge_w_parent: EdgeWithParent::AppToArg(app_index),
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

    pub fn abs(body: DebruijnEdge, usage: usize) -> DebruijnNode {
        DebruijnNode::Abstraction(Abstraction { body, usage })
    }

    pub fn app(func: DebruijnEdge, arg: DebruijnEdge) -> DebruijnNode {
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

// The path of edges from the root to a node
#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct ParentChain {
    // Every edge in this vector is a abs -> body edge
    pub abstractions: Vec<DoubleEndedEdge>,
    full_chain: Vec<DoubleEndedEdge>,
}

impl ParentChain {
    pub fn new(root: &FlatRoot) -> ParentChain {
        ParentChain {
            abstractions: vec![],
            full_chain: vec![DoubleEndedEdge::root(root)],
        }
    }
    pub fn push(&mut self, edge: DoubleEndedEdge) {
        if matches!(edge.edge_w_parent, EdgeWithParent::AbsToBody(_)) {
            self.abstractions.push(edge);
        }
        self.full_chain.push(edge);
    }
    pub fn pop(&mut self, edge: DoubleEndedEdge) {
        if matches!(edge.edge_w_parent, EdgeWithParent::AbsToBody(_)) {
            self.abstractions.pop();
        }
        self.full_chain.pop();
    }

    pub fn debruijn_depth(&self) -> DebruijnDepth {
        self.abstractions.len()
    }

    fn total_adjust(&self, index: usize) -> isize {
        // this effectively applies shift_cutoff on the spot
        // each non-None adjustment value is equivalent to shift_cutoff of that amount, at the given
        // depth (meaning we only apply the adjustment value if this index is bound with respect to
        // the the given parent node)
        let mut current_depth = 0;
        let mut total_adjust = 0;
        for edge in self.full_chain.iter().cloned() {
            // indicies which are greater or equal to this value are considered free
            // This means as we decend, the threshold decreases
            let threshold = self.debruijn_depth() - current_depth;
            let is_free = threshold < index;

            if let Some(adjust) = edge.adjust
                && is_free
            {
                total_adjust += adjust;
            }

            if matches!(edge.edge_w_parent, EdgeWithParent::AbsToBody(_)) {
                current_depth += 1;
            }
        }
        total_adjust
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct RedexMut {
    // The entire chain of abstractions for the parent, which will all need to get fixed up during substitution.
    parent_chain: ParentChain,
    // Application term for the redex. If the parent for this is none,
    // then the Redex is actually the root (and therefore is pointed to by FlatRoot.root)
    pub app: DoubleEndedEdge,
    // The Abstraction containing the body. This must be an Abstraction
    pub abs: DebruijnEdge,
    // The body of the Abstraction. This must be pointed to by `abs`
    body: DoubleEndedEdge,
    // The argument of the Application. This must be pointed to by `app.arg`
    pub arg: DebruijnEdge,
    // The usage of the `body`. Provided for convinence
    body_usage: Usage,
}

impl RedexMut {
    pub fn is_redex(root: &FlatRoot, term: BackingIndex) -> bool {
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
                    let body = abs.body(app.func.child);
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

    fn arg(&self) -> DoubleEndedEdge {
        DoubleEndedEdge {
            child: self.arg.child,
            adjust: self.app.adjust,
            edge_w_parent: EdgeWithParent::AppToArg(self.app.child),
        }
    }

    fn abs(&self) -> DoubleEndedEdge {
        DoubleEndedEdge {
            child: self.abs.child,
            adjust: self.app.adjust,
            edge_w_parent: EdgeWithParent::AppToFunc(self.app.child),
        }
    }

    fn arg_ctx(&'_ mut self) -> ActionCtx<'_> {
        ActionCtx {
            term: self.arg(),
            chain: &mut self.parent_chain,
        }
    }

    fn func_ctx(&'_ mut self) -> ActionCtx<'_> {
        ActionCtx {
            term: self.abs(),
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
    repoint_node(root, redex.app.edge_w_parent, body);
    // Now that parent points to body, we need to fix up the parent -> body adjustment value
    // This is because it's possible for the app -> abs edge to have a subterm adjustment value

    let existing_adjust = redex.app.adjust;
    let app_abs_adjust = root.get_app(redex.app.child).func.adjust;
    let new_adjustment = add(existing_adjust, app_abs_adjust);
    set_adjustment(root, redex.app.edge_w_parent, new_adjustment);
    // TODO: Should the parent -> app and abs -> body edges also be included here?
}

fn set_adjustment(root: &mut FlatRoot, edge: EdgeWithParent, new_adjustment: Adjustment) {
    match edge {
        EdgeWithParent::AbsToBody(parent) => {
            let mut abs = root.get_abs(parent);
            abs.body.adjust = new_adjustment;
            root[parent] = DebruijnNode::Abstraction(abs);
        }
        EdgeWithParent::AppToFunc(parent) => {
            let mut app = root.get_app(parent);
            app.func.adjust = new_adjustment;
            root[parent] = DebruijnNode::Application(app);
        }
        EdgeWithParent::AppToArg(parent) => {
            let mut app = root.get_app(parent);
            app.arg.adjust = new_adjustment;
            root[parent] = DebruijnNode::Application(app);
        }
        EdgeWithParent::IntoRoot => {
            root.root.adjust = new_adjustment;
        }
    }
}

fn add(a: Adjustment, b: Adjustment) -> Adjustment {
    match (a, b) {
        (None, None) => None,
        (None, Some(b)) => Some(b),
        (Some(a), None) => Some(a),
        (Some(a), Some(b)) => Some(a + b),
    }
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
    for (depth, edge) in ctx.chain.abstractions.iter().enumerate() {
        // Unwrap is safe here because all of the values in the ctx.chain.abstractions iterator
        // are AbsToBody values.
        let parent = edge.parent_index().unwrap();
        let abs = root.get_abs(parent);

        let usage_of_parent_in_arg = usages_of_page_in_arg[depth];
        let usage_delta: isize = (body_usage as isize - 1) * usage_of_parent_in_arg as isize;
        let usage = abs.usage.checked_add_signed(usage_delta).unwrap();
        root[parent] = DebruijnNode::abs(abs.body, usage)
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
/// Example
///
///     parent   <- parent               old parent
///       |      <- parent      child ->     |
///  old child                  child ->   new child
///
/// This will become:
///
/// parent                 old parent <- garbage
///   |
/// child                  old child <- garbage
///
/// MEMORY: Old child becomes garbage after repointing.
fn repoint_node(root: &mut FlatRoot, parent: EdgeWithParent, child: DebruijnEdge) {
    match parent {
        EdgeWithParent::AbsToBody(parent) => {
            let abs = root.get_abs(parent);
            root[parent] = DebruijnNode::abs(child, abs.usage)
        }
        EdgeWithParent::AppToFunc(parent) => {
            let app = root.get_app(parent);
            root[parent] = DebruijnNode::app(child, app.arg);
        }
        EdgeWithParent::AppToArg(parent) => {
            let app = root.get_app(parent);
            root[parent] = DebruijnNode::app(app.func, child)
        }
        // Root
        EdgeWithParent::IntoRoot => {
            root.root = child;
        }
    }
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
fn substitute_and_shift_fused(root: &mut FlatRoot, redex: &mut RedexMut) -> DebruijnEdge {
    if redex.body_usage == 0 {
        // No need to do anything with the argument because it is never used in the body
        // (Since the argument is not used, the entire arg subtree is garbage now.)
        // Fix up the indicies in it to account for the fact that we are still dropping out the abstraction that the body is in.
        down_one(root, &mut redex.func_ctx());
        let abs = root.get_abs(redex.abs.child);
        abs.body
        // DebruijnEdge {
        //     index: body,
        //     adjust: Some(-1),
        // }
    } else {
        // Otherwise, perform substitution as usual

        // Perform the actual substition on body.
        // This method actually fuses the fixing down/up that needs to happen for the whole body
        // in addition to performing substitutions.
        substitute_shift_fused_nonzero_usage(root, redex);

        // The body of abs may get repointed if the redex body consists of a single leaf node that gets substituted.
        // Hence, we need to check for this and get the actually new body.
        root.get_abs(redex.abs.child).body
    }
}

fn substitute_shift_fused_nonzero_usage(root: &mut FlatRoot, redex: &mut RedexMut) {
    let mut substitution_i = 0;
    let init_depth = redex.parent_chain.debruijn_depth();

    let mut redex2 = redex.clone();
    let arg_ctx = &mut redex2.arg_ctx();
    let redex_arg = redex.arg;
    let body_usage = redex.body_usage;
    root.preorder_walk_at_mut(&mut redex.func_ctx(), |root, ctx| {
        let term = ctx.term;
        let chain = &ctx.chain;
        if let DebruijnNode::Index(debruijn_index) = root[term] {
            let depth_relative_to_arg = chain.debruijn_depth() - init_depth;
            // Note that the depth here is 0-indexed, while debruijn_index is 1-indexed
            let calculated_index = debruijn_index.get(chain);
            let is_substituting = calculated_index == depth_relative_to_arg;
            if is_substituting {
                let last_arg_allocation = substitution_i == body_usage - 1;
                let new_arg = if last_arg_allocation {
                    // Optimization opportunity: Instead of making `arg` become garbage, instead reuse it and avoid doing one alloc.
                    // Bump up free variables by `depth`
                    // Note that normally we would have fixed up the argument by one prior to
                    // calling this method. However, we also fix down the entire body by one after
                    // calling the method. Both of these fixups cancel out, so we still only just
                    // fix up by `depth`
                    up_by(root, arg_ctx, depth_relative_to_arg - 1);
                    redex_arg
                } else {
                    clone_subtree_and_fix_up_fused(root, arg_ctx, depth_relative_to_arg - 1)
                };
                // Point parent to the newly created subtree
                // TODO: Does adjustment need to be inherited here?
                repoint_node(root, term.edge_w_parent, new_arg);
                substitution_i += 1;
            } else if calculated_index > depth_relative_to_arg {
                // Variable is a free variable, but is NOT getting substituted.
                // Remember that the body of the term is getting dropped out of the abstraction
                // Because of this, we need to reduce the term_index by one, since there's one
                // less abstraction to jump over for the index.
                root[term] = DebruijnNode::idx(calculated_index - 1);
            }
        }
    });
    assert_eq!(
        substitution_i, redex.body_usage,
        "Expected substitution count ({}) to equal usage ({})!",
        substitution_i, redex.body_usage
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
) -> DebruijnEdge {
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
        let term = ctx.term.child;
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
            term: DoubleEndedEdge::root(root),
            chain: &mut ParentChain::new(root),
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
