use core::fmt;
use std::{
    collections::HashMap,
    fmt::{Binary, Display},
    num::NonZeroUsize,
    ops::{Index, IndexMut},
    str::FromStr,
    usize,
};

use crate::{debruijn::Debruijn, graphviz};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FlatTree {
    pub backing: Vec<DebruijnNode>,
    // The into-root edge, which has no parent and whose child is the root node itself
    // --> root
    pub root: BackingIndex,
}
impl FlatTree {
    fn new() -> FlatTree {
        FlatTree {
            backing: vec![],
            root: BackingIndex(0),
        }
    }

    // Allocate a dummy node and return the backing index to the dummy.
    // This dummy node should be set to something reasonable.
    fn alloc_none(&mut self) -> BackingIndex {
        let backing_index = BackingIndex(self.backing.len());
        let dummy = DebruijnNode::Index(Binding::Bound(BackingIndex(usize::MAX)));
        self.backing.push(dummy);
        backing_index
    }

    /// Allocate the given term onto the backing vector. The node is set to the node
    /// in the input `term`.
    /// The return value is the index to the newly allocated node.
    fn alloc(&mut self, term: DebruijnNode) -> BackingIndex {
        let term_index = BackingIndex(self.backing.len());
        self.backing.push(term);
        term_index
    }

    pub fn normalized(&self) -> FlatTree {
        struct Context<'a> {
            old_tree: &'a FlatTree,
            new_tree: &'a mut FlatTree,
            old_abstraction_chain: Vec<BackingIndex>,
            new_abstraction_chain: Vec<BackingIndex>,
        }

        fn _normalize(ctx: &mut Context, old_node_index: BackingIndex) -> BackingIndex {
            match ctx.old_tree[old_node_index] {
                DebruijnNode::Index(binding) => {
                    let binding = match binding {
                        Binding::Free(_) => binding,
                        Binding::Bound(backing_index) => {
                            let debruijn_depth = ctx
                                .old_abstraction_chain
                                .iter()
                                .position(|old_abs_idx| *old_abs_idx == backing_index)
                                .unwrap();

                            let new_abstraction_index = ctx.new_abstraction_chain[debruijn_depth];

                            Binding::Bound(new_abstraction_index)
                        }
                    };

                    let index = DebruijnNode::idx(binding);
                    ctx.new_tree.alloc(index)
                }
                DebruijnNode::Abstraction(abstraction) => {
                    let old_body_index = abstraction.body;
                    let old_usage = abstraction.usage;

                    let new_abstraction_index = ctx.new_tree.alloc_none();

                    ctx.old_abstraction_chain.push(old_node_index);
                    ctx.new_abstraction_chain.push(new_abstraction_index);

                    let new_body = _normalize(ctx, old_body_index);

                    ctx.old_abstraction_chain.pop();
                    ctx.new_abstraction_chain.pop();

                    let new_abstraction = DebruijnNode::abs(new_body, old_usage);
                    ctx.new_tree[new_abstraction_index] = new_abstraction;

                    new_abstraction_index
                }
                DebruijnNode::Application(application) => {
                    let old_func_index = application.func;
                    let old_arg_index = application.arg;

                    let new_func = _normalize(ctx, old_func_index);
                    let new_arg = _normalize(ctx, old_arg_index);

                    let app = DebruijnNode::app(new_func, new_arg);
                    let app_index = ctx.new_tree.alloc(app);
                    app_index
                }
            }
        }

        let mut new_tree = FlatTree::new();

        let mut ctx = Context {
            old_tree: self,
            new_tree: &mut new_tree,
            old_abstraction_chain: vec![],
            new_abstraction_chain: vec![],
        };

        let root_node = _normalize(&mut ctx, self.root);
        new_tree.root = root_node;
        new_tree
    }

    pub fn check_usage(&self) -> Result<(), (BackingIndex, Usage, Usage)> {
        fn _check_usage(
            tree: &FlatTree,
            index: BackingIndex,
        ) -> Result<(), (BackingIndex, Usage, Usage)> {
            match tree[index] {
                DebruijnNode::Index(_) => (),
                DebruijnNode::Abstraction(abstraction) => {
                    let expected = compute_usage_flat(tree, index);
                    let actual = abstraction.usage;
                    if actual != expected {
                        return Err((index, actual, expected));
                    }
                    _check_usage(tree, abstraction.body)?;
                }
                DebruijnNode::Application(application) => {
                    _check_usage(tree, application.func)?;
                    _check_usage(tree, application.arg)?;
                }
            }
            Ok(())
        }
        _check_usage(self, self.root)
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

impl FromStr for FlatTree {
    type Err = <Debruijn as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(FlatTree::from(&Debruijn::from_str(s)?))
    }
}

impl Display for FlatTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&Debruijn::from(self), f)
    }
}

impl Binary for FlatTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Binary::fmt(&Debruijn::from(self), f)
    }
}

impl Index<BackingIndex> for FlatTree {
    type Output = DebruijnNode;

    fn index(&self, index: BackingIndex) -> &Self::Output {
        &self.backing[index.0]
    }
}

impl IndexMut<BackingIndex> for FlatTree {
    fn index_mut(&mut self, index: BackingIndex) -> &mut Self::Output {
        &mut self.backing[index.0]
    }
}

impl Index<DoubleEndedEdge> for FlatTree {
    type Output = DebruijnNode;

    fn index(&self, index: DoubleEndedEdge) -> &Self::Output {
        &self[index.child]
    }
}

impl IndexMut<DoubleEndedEdge> for FlatTree {
    fn index_mut(&mut self, index: DoubleEndedEdge) -> &mut Self::Output {
        &mut self[index.child]
    }
}

impl From<Vec<DebruijnNode>> for FlatTree {
    fn from(backing: Vec<DebruijnNode>) -> Self {
        FlatTree {
            backing,
            root: BackingIndex(0),
        }
    }
}

impl From<Debruijn> for FlatTree {
    fn from(value: Debruijn) -> Self {
        FlatTree::from(&value)
    }
}

impl From<&Debruijn> for FlatTree {
    fn from(term: &Debruijn) -> Self {
        fn compute_binding(abstraction_chain: &[BackingIndex], debruijn_index: usize) -> Binding {
            if debruijn_index > abstraction_chain.len() {
                let free_height = debruijn_index - abstraction_chain.len();
                Binding::Free(NonZeroUsize::new(free_height).unwrap())
            } else {
                let chain_index = abstraction_chain.len() - debruijn_index;
                Binding::Bound(abstraction_chain[chain_index])
            }
        }

        fn flatten(
            tree: &mut FlatTree,
            abstraction_chain: &mut Vec<BackingIndex>,
            term: &Debruijn,
        ) -> BackingIndex {
            let term = match term {
                Debruijn::Index(index) => {
                    let binding = compute_binding(abstraction_chain, *index);
                    DebruijnNode::idx(binding)
                }
                Debruijn::Abstraction { body } => {
                    let usage = compute_usage(&body);

                    // Pre-allocation is needed here so that we can have a spot for the abstraction
                    // node to reside in. We will need this value to be allocated by the time we
                    // go to compute the binding for any index nodes that depend on it.
                    let backing_index = tree.alloc_none();

                    abstraction_chain.push(backing_index);
                    let body = flatten(tree, abstraction_chain, body);
                    abstraction_chain.pop();

                    tree[backing_index] = DebruijnNode::abs(body, usage);
                    return backing_index;
                }
                Debruijn::Application { func, arg } => {
                    let func = flatten(tree, abstraction_chain, func);
                    let arg = flatten(tree, abstraction_chain, arg);
                    DebruijnNode::app(func, arg)
                }
            };
            tree.alloc(term)
        }

        let mut tree = FlatTree::new();
        let root_index = flatten(&mut tree, &mut vec![], term);
        tree.root = root_index;
        tree
    }
}

impl From<&FlatTree> for Debruijn {
    fn from(tree: &FlatTree) -> Self {
        struct Context<'a> {
            tree: &'a FlatTree,
            abstraction_chain: Vec<BackingIndex>,
        }
        fn _from(ctx: &mut Context, index: BackingIndex) -> Debruijn {
            match ctx.tree[index] {
                DebruijnNode::Index(binding) => {
                    let debruijn_index = compute_debruijn_index(&ctx.abstraction_chain, binding);
                    Debruijn::Index(debruijn_index)
                }
                DebruijnNode::Abstraction(abstraction) => {
                    ctx.abstraction_chain.push(index);
                    let body = _from(ctx, abstraction.body);
                    ctx.abstraction_chain.pop();
                    Debruijn::Abstraction {
                        body: Box::new(body),
                    }
                }
                DebruijnNode::Application(application) => {
                    let func = _from(ctx, application.func);
                    let arg: Debruijn = _from(ctx, application.arg);
                    Debruijn::Application {
                        func: Box::new(func),
                        arg: Box::new(arg),
                    }
                }
            }
        }

        let mut ctx = Context {
            tree,
            abstraction_chain: vec![],
        };
        _from(&mut ctx, tree.root)
    }
}

pub fn compute_debruijn_index(abstraction_chain: &[BackingIndex], binding: Binding) -> usize {
    let debruijn_depth = abstraction_chain.len();
    match binding {
        Binding::Bound(backing_index) => {
            let index = abstraction_chain
                .iter()
                .position(|abstraction_index| *abstraction_index == backing_index)
                .unwrap();
            debruijn_depth - index
        }
        Binding::Free(free_height) => debruijn_depth + free_height.get(),
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
pub fn compute_usage_flat(tree: &FlatTree, abstraction_index: BackingIndex) -> Usage {
    fn _compute_usage_flat(
        tree: &FlatTree,
        abstraction_index: BackingIndex,
        index: BackingIndex,
    ) -> Usage {
        match tree[index] {
            DebruijnNode::Index(binding) => {
                if binding.is_bound_to(abstraction_index) {
                    1
                } else {
                    0
                }
            }
            DebruijnNode::Abstraction(abstraction) => {
                _compute_usage_flat(tree, abstraction_index, abstraction.body)
            }
            DebruijnNode::Application(application) => {
                _compute_usage_flat(tree, abstraction_index, application.func)
                    + _compute_usage_flat(tree, abstraction_index, application.arg)
            }
        }
    }

    let abstraction = tree.get_abs(abstraction_index);
    _compute_usage_flat(tree, abstraction_index, abstraction.body)
}

// The depth relative to some term. This is used to determine if a variable is free within a term
// If a given Index node has a DebruijnIndex >= DebruijnDepth, then that Index node is a free variable
// with respect to that subtree)
// Zero indicates that there are no abstractions between the two terms, one indicates one abstraction, etc
pub type DebruijnDepth = usize;

// The number of times a variable is used in an abstraction.
pub type Usage = usize;

/// A pointer to a given DebruijnNode within a FlatTree
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BackingIndex(pub usize);

impl Display for BackingIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}", self.0)
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
    pub fn backing_index(&self) -> Option<BackingIndex> {
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
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct DoubleEndedEdge {
    pub edge_w_parent: EdgeWithParent,
    pub child: BackingIndex,
}
impl DoubleEndedEdge {
    pub fn root(tree: &FlatTree) -> DoubleEndedEdge {
        DoubleEndedEdge {
            edge_w_parent: EdgeWithParent::IntoRoot,
            child: tree.root,
        }
    }

    pub fn parent_index(&self) -> Option<BackingIndex> {
        self.edge_w_parent.backing_index()
    }
}
impl std::fmt::Debug for DoubleEndedEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let edge_type = match self.edge_w_parent {
            EdgeWithParent::IntoRoot => "into_root",
            EdgeWithParent::AbsToBody(_) => "abs_to_body",
            EdgeWithParent::AppToFunc(_) => "app_to_func",
            EdgeWithParent::AppToArg(_) => "app_to_arg",
        };
        let child = self.child;
        match self.edge_w_parent.backing_index() {
            Some(parent) => write!(f, "{edge_type}: {parent} -> {child}")?,
            None => write!(f, "{edge_type}: [root] -> {child}")?,
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Abstraction {
    // The index of the body of the abstraction
    pub body: BackingIndex,
    /// Number of times the input argument is used in the body
    /// If this is zero, then when doing argument substitution, the algorithm can just
    /// return the body and throw away the argument!
    /// This value is constant over the lifetime of the Abstraction (this will become not true if
    /// we do "partial" substition where not all usages of the input argument are substituted)
    pub usage: Usage,
}

impl Abstraction {
    // Returns a double ended edge for this Abstraction
    // abs --> body
    // abs_index should be the index of the abstraction node.
    pub fn abs_to_body(&self, abs_index: BackingIndex) -> DoubleEndedEdge {
        DoubleEndedEdge {
            child: self.body,
            edge_w_parent: EdgeWithParent::AbsToBody(abs_index),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Application {
    pub func: BackingIndex,
    pub arg: BackingIndex,
}

impl Application {
    pub fn func(&self, app_index: BackingIndex) -> DoubleEndedEdge {
        DoubleEndedEdge {
            child: self.func,
            edge_w_parent: EdgeWithParent::AppToFunc(app_index),
        }
    }

    pub fn arg(&self, app_index: BackingIndex) -> DoubleEndedEdge {
        DoubleEndedEdge {
            child: self.arg,
            edge_w_parent: EdgeWithParent::AppToArg(app_index),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Binding {
    // The backing index of the abstraction that the Index node binds to
    Bound(BackingIndex),
    // The number of abstractions above the root that this Index node binds to
    // For example, in λ x, if x = 2, then we have a free bind of 1
    // If x = 3, then we have a free bind of 2, and so on.
    // Zero is not a valid value for this because we start 1-indexed
    // Note that this is NOT a debruijn index, it's a debruijn depth, as it always refers
    // to a constant number of abstractions above the root, no matter how deeply nested the
    // actual index is
    Free(NonZeroUsize),
}

impl Display for Binding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Binding::Bound(backing_index) => write!(f, "{backing_index}"),
            Binding::Free(free_index) => write!(f, "free ({free_index})"),
        }
    }
}

impl Binding {
    fn is_bound_to(&self, backing_index: BackingIndex) -> bool {
        *self == Binding::Bound(backing_index)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum DebruijnNode {
    // This backing index points to the abstraction that this index binds to
    Index(Binding),
    Abstraction(Abstraction),
    Application(Application),
}
impl DebruijnNode {
    pub fn idx(binding: Binding) -> DebruijnNode {
        DebruijnNode::Index(binding)
    }

    pub fn abs(body: BackingIndex, usage: usize) -> DebruijnNode {
        DebruijnNode::Abstraction(Abstraction { body, usage })
    }

    pub fn app(func: BackingIndex, arg: BackingIndex) -> DebruijnNode {
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
            Self::Index(index) => write!(f, "idx: {}", index),
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
    pub full_chain: Vec<DoubleEndedEdge>,
}

impl ParentChain {
    pub fn new(tree: &FlatTree) -> ParentChain {
        ParentChain {
            abstractions: vec![],
            full_chain: vec![DoubleEndedEdge::root(tree)],
        }
    }
    #[track_caller]
    pub fn push(&mut self, edge: DoubleEndedEdge) {
        // Sanity check - we expect the previous edge's child to match up with
        // this edge's parent. If not, we've broken the chain somehow

        // This unwrap is safe because even an "empty" chain will have the into-root
        // edge.
        let last_edge = self.full_chain.last().unwrap();
        let last_edge_child = last_edge.child;
        // This unwrap is safe because only the into-root edge will not have a parent
        // and we never allow pushing the into-root edge in this method.
        let this_edge_parent = edge.parent_index().unwrap();
        assert_eq!(
            last_edge_child, this_edge_parent,
            "Incorrect edge pushed. Chain: {self:#?}, edge: {edge:?}"
        );

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
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct RedexMut {
    // The number of abstractions in the parent chain above this redex
    debruijn_depth: DebruijnDepth,

    parent_to_app: EdgeWithParent,
    // The index of the redex application node
    pub app_index: BackingIndex,
    // The left child of the redex's application node. This should be an abstraction node
    pub func_index: BackingIndex,
    // The child of the left child of the redex application
    body_index: BackingIndex,
    // The right child of the redex's application node.
    pub arg_index: BackingIndex,
    // The usage of the `body`. Provided for convinence
    body_usage: Usage,
}

impl RedexMut {
    pub fn is_redex(tree: &FlatTree, term: BackingIndex) -> bool {
        match tree[term] {
            DebruijnNode::Application(app) => match tree[app.func] {
                DebruijnNode::Abstraction { .. } => true,
                _ => false,
            },
            _ => false,
        }
    }

    pub fn try_get(
        tree: &FlatTree,
        debruijn_depth: DebruijnDepth,
        parent_to_app: EdgeWithParent,
        app_index: BackingIndex,
    ) -> Option<RedexMut> {
        match tree[app_index] {
            DebruijnNode::Application(app) => match tree[app.func] {
                DebruijnNode::Abstraction(abs) => {
                    let redex = RedexMut {
                        debruijn_depth,
                        parent_to_app,
                        app_index,
                        func_index: app.func,
                        body_index: abs.body,
                        arg_index: app.arg,
                        body_usage: abs.usage,
                    };
                    Some(redex)
                }
                _ => None,
            },
            _ => None,
        }
    }
}

pub enum WalkResult {
    StackIsEmpty,
    None,
    Some(RedexMut),
}

pub struct WalkContext {
    stack: Vec<(BackingIndex, EdgeWithParent, DebruijnDepth)>,
}

impl WalkContext {
    pub fn new(tree: &FlatTree) -> WalkContext {
        WalkContext {
            stack: vec![(tree.root, EdgeWithParent::IntoRoot, 0)],
        }
    }

    pub fn walk_one(&mut self, tree: &FlatTree) -> WalkResult {
        if let Some((index, parent_to_current, depth)) = self.stack.pop() {
            match tree[index] {
                DebruijnNode::Index(_) => WalkResult::None,
                DebruijnNode::Abstraction(abstraction) => {
                    let next_body = (
                        abstraction.body,
                        EdgeWithParent::AbsToBody(index),
                        depth + 1,
                    );
                    self.stack.push(next_body);
                    WalkResult::None
                }
                DebruijnNode::Application(application) => {
                    // Note that we want func to be visited before arg--it turns out that most of the
                    // time, redexes live in the function half rather than the argument half.
                    let next_arg = (application.arg, EdgeWithParent::AppToArg(index), depth);
                    self.stack.push(next_arg);

                    let next_func = (application.func, EdgeWithParent::AppToFunc(index), depth);
                    self.stack.push(next_func);

                    if let Some(redex) = RedexMut::try_get(tree, depth, parent_to_current, index) {
                        WalkResult::Some(redex)
                    } else {
                        WalkResult::None
                    }
                }
            }
        } else {
            WalkResult::StackIsEmpty
        }
    }
}

impl FlatTree {
    pub fn get_redexes(&self) -> Vec<RedexMut> {
        struct Context<'a> {
            tree: &'a FlatTree,
            debruijn_depth: DebruijnDepth,
            redexes: Vec<RedexMut>,
        }

        fn _get_redexes(ctx: &mut Context, index: BackingIndex, parent_to_current: EdgeWithParent) {
            match ctx.tree[index] {
                DebruijnNode::Index(_) => (),
                DebruijnNode::Abstraction(abstraction) => {
                    ctx.debruijn_depth += 1;
                    _get_redexes(ctx, abstraction.body, EdgeWithParent::AbsToBody(index));
                    ctx.debruijn_depth -= 1;
                }
                DebruijnNode::Application(application) => {
                    if let Some(redex) =
                        RedexMut::try_get(ctx.tree, ctx.debruijn_depth, parent_to_current, index)
                    {
                        ctx.redexes.push(redex);
                    }
                    _get_redexes(ctx, application.func, EdgeWithParent::AppToFunc(index));
                    _get_redexes(ctx, application.arg, EdgeWithParent::AppToArg(index));
                }
            }
        }

        let mut ctx = Context {
            tree: self,
            debruijn_depth: 0,
            redexes: vec![],
        };
        _get_redexes(&mut ctx, self.root, EdgeWithParent::IntoRoot);
        ctx.redexes
    }

    pub fn is_bnf(&self) -> bool {
        let mut ctx = WalkContext::new(self);
        loop {
            match ctx.walk_one(self) {
                WalkResult::StackIsEmpty => return true,
                WalkResult::Some(_) => return false,
                WalkResult::None => continue,
            }
        }
    }
}

pub fn beta_reduce(tree: &mut FlatTree, mut redex: RedexMut) {
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

    update_usages(tree, &mut redex);

    // This is the following tree fragment
    // --> new_body
    // (the parent to this edge is supposed to be abs, although this will change later in this methods)
    // Note that body may have been re-allocated--this happens when the body consists of a single
    // leaf node that gets substituted--aka: the abstraction node looks like λ 1
    let new_body = substitute(tree, &mut redex);

    // Finally, make the parent point to the body, causing `app` and `abs` to be garbage.
    // The app and abs nodes are no longer pointed to by anything, and therefore are now garbage.
    // The tree now looks like this
    //   parent------+
    //               |
    //               |
    //    app        |
    //   /   \       |
    //  V     V      |   (not shown: the potentially garbage body node)
    // abs   arg     |   (new_body may actually just be the existing body)
    //               |   (or it could be a new node.)
    //               |
    // new_body <----+
    //  ||
    //  VV
    // [various copies of arg]
    repoint_node(tree, redex.parent_to_app, new_body);
}

// Updates the usages of the parent chain.
// MEMORY: Modifies in place, does not allocate or make garbage.
fn update_usages(tree: &mut FlatTree, redex: &RedexMut) {
    // If there are no parents to update (which happens if the redex is the root)
    // or otherwise has no abstractions in it's parent path, then do nothing.
    if redex.debruijn_depth == 0 {
        return;
    }

    let index_to_usage_in_arg = get_usage_by_depth(tree, redex.arg_index);
    for (abstraction_index, usage_in_arg) in index_to_usage_in_arg {
        let abs = tree.get_abs(abstraction_index);

        let usage_delta: isize = (redex.body_usage as isize - 1) * usage_in_arg as isize;
        let usage = abs.usage.checked_add_signed(usage_delta).unwrap();

        tree[abstraction_index] = DebruijnNode::abs(abs.body, usage)
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
fn get_usage_by_depth(tree: &FlatTree, arg_index: BackingIndex) -> HashMap<BackingIndex, Usage> {
    struct Context<'a> {
        tree: &'a FlatTree,
        usages: HashMap<BackingIndex, Usage>,
        arg_subtree_abstractions: Vec<BackingIndex>,
    }
    fn _get_usage_by_depth(ctx: &mut Context, index: BackingIndex) {
        match ctx.tree[index] {
            DebruijnNode::Index(binding) => {
                if let Binding::Bound(backing_index) = binding {
                    // We don't update usages for abstractions inside the argument subtree
                    // This is because those abstractions will be duplicated and therefore not have
                    // their usages change at all. Hence we need to check that the backing index
                    // is binding to some abstraction in the arg abstraction chain and not just any
                    // abstraction
                    let bound_within_arg = ctx.arg_subtree_abstractions.contains(&backing_index);
                    if !bound_within_arg {
                        let entry = ctx.usages.entry(backing_index).or_insert(0);
                        *entry += 1;
                    }
                }
            }
            DebruijnNode::Abstraction(abstraction) => {
                ctx.arg_subtree_abstractions.push(index);
                _get_usage_by_depth(ctx, abstraction.body);
                ctx.arg_subtree_abstractions.pop();
            }
            DebruijnNode::Application(application) => {
                _get_usage_by_depth(ctx, application.func);
                _get_usage_by_depth(ctx, application.arg);
            }
        }
    }

    let mut ctx = Context {
        tree,
        usages: HashMap::new(),
        arg_subtree_abstractions: vec![],
    };

    _get_usage_by_depth(&mut ctx, arg_index);

    ctx.usages
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
fn repoint_node(tree: &mut FlatTree, parent: EdgeWithParent, child: BackingIndex) {
    if parent.backing_index() == Some(child) {
        graphviz::debug_write_to_file(tree, "bad_repoint");
        panic!("attempt to repoint {parent:?} to {child} which would cause a loop (tree: {tree:?}");
    }
    match parent {
        EdgeWithParent::AbsToBody(parent) => {
            let abs = tree.get_abs(parent);
            tree[parent] = DebruijnNode::abs(child, abs.usage);
        }
        EdgeWithParent::AppToFunc(parent) => {
            let app = tree.get_app(parent);
            tree[parent] = DebruijnNode::app(child, app.arg);
        }
        EdgeWithParent::AppToArg(parent) => {
            let app = tree.get_app(parent);
            tree[parent] = DebruijnNode::app(app.func, child);
        }
        EdgeWithParent::IntoRoot => tree.root = child,
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
fn substitute(tree: &mut FlatTree, redex: &mut RedexMut) -> BackingIndex {
    if redex.body_usage == 0 {
        // No need to do anything with the argument because it is never used in the body
        // (Since the argument is not used, the entire arg subtree is garbage now.)
        redex.body_index
    } else {
        // Otherwise, perform substitution as usual
        substitute_nonzero_usage(tree, redex);

        // The body of abs may get repointed if the redex body consists of a single leaf node that gets substituted.
        // Hence, we need to check for this and get the actually new body.
        tree.get_abs(redex.func_index).body
    }
}

fn substitute_nonzero_usage(tree: &mut FlatTree, redex: &mut RedexMut) {
    struct Context<'a> {
        tree: &'a mut FlatTree,
        substitution_i: usize,
        func_index: BackingIndex,
        arg_index: BackingIndex,
        body_usage: Usage,
    }

    fn _substitute(ctx: &mut Context, node_index: BackingIndex, parent_to_node: EdgeWithParent) {
        match ctx.tree[node_index] {
            DebruijnNode::Index(binding) => {
                let is_substituting = binding.is_bound_to(ctx.func_index);
                if is_substituting {
                    // Optimization opportunity: Instead of making `arg` become garbage, instead reuse it and avoid doing one alloc.
                    let last_arg_allocation = ctx.substitution_i == ctx.body_usage - 1;
                    let new_child = if last_arg_allocation {
                        ctx.arg_index
                    } else {
                        clone_subtree(ctx.tree, ctx.arg_index)
                    };

                    // Point parent to the newly created subtree
                    repoint_node(ctx.tree, parent_to_node, new_child);
                    ctx.substitution_i += 1;
                }
            }
            DebruijnNode::Abstraction(abstraction) => {
                _substitute(ctx, abstraction.body, EdgeWithParent::AbsToBody(node_index))
            }
            DebruijnNode::Application(application) => {
                _substitute(ctx, application.func, EdgeWithParent::AppToFunc(node_index));
                _substitute(ctx, application.arg, EdgeWithParent::AppToArg(node_index));
            }
        }
    }

    let mut ctx = Context {
        tree,
        substitution_i: 0,
        func_index: redex.func_index,
        body_usage: redex.body_usage,
        arg_index: redex.arg_index,
    };

    _substitute(
        &mut ctx,
        redex.body_index,
        EdgeWithParent::AbsToBody(redex.func_index),
    );

    assert_eq!(
        ctx.substitution_i, redex.body_usage,
        "Expected substitution count ({}) to equal usage ({})!",
        ctx.substitution_i, redex.body_usage
    );
}

/// Clone the given subtree.
///
/// MEMORY: Allocates new subtree, returned value is the newly allocated tree
fn clone_subtree(tree: &mut FlatTree, index: BackingIndex) -> BackingIndex {
    struct Context<'a> {
        tree: &'a mut FlatTree,
        old_abstraction_chain: Vec<BackingIndex>,
        new_abstraction_chain: Vec<BackingIndex>,
    }

    fn _clone_subtree(ctx: &mut Context<'_>, old_node_index: BackingIndex) -> BackingIndex {
        match ctx.tree[old_node_index] {
            DebruijnNode::Index(binding) => {
                let binding = match binding {
                    Binding::Free(_) => binding,
                    Binding::Bound(backing_index) => {
                        let debruijn_depth = ctx
                            .old_abstraction_chain
                            .iter()
                            .position(|old_abs_idx| *old_abs_idx == backing_index);

                        if let Some(debruijn_depth) = debruijn_depth {
                            // If this is some, then the binding is bound within the subtree being cloned
                            // In this case, the binding needs to be updated to point to the abstraction
                            // in the cloned subtree.
                            let new_abstraction_index = ctx.new_abstraction_chain[debruijn_depth];
                            Binding::Bound(new_abstraction_index)
                        } else {
                            // Otherwise, the binding is bound within the tree but outside of the subtree bieng cloned.
                            // In that case, there is no need to update the binding
                            binding
                        }
                    }
                };

                let index = DebruijnNode::idx(binding);
                ctx.tree.alloc(index)
            }
            DebruijnNode::Abstraction(abstraction) => {
                let old_body_index = abstraction.body;
                let old_usage = abstraction.usage;

                let new_abstraction_index = ctx.tree.alloc_none();

                ctx.old_abstraction_chain.push(old_node_index);
                ctx.new_abstraction_chain.push(new_abstraction_index);

                let new_body = _clone_subtree(ctx, old_body_index);

                ctx.old_abstraction_chain.pop();
                ctx.new_abstraction_chain.pop();

                let new_abstraction = DebruijnNode::abs(new_body, old_usage);
                ctx.tree[new_abstraction_index] = new_abstraction;

                new_abstraction_index
            }
            DebruijnNode::Application(application) => {
                let old_func_index = application.func;
                let old_arg_index = application.arg;

                let new_func = _clone_subtree(ctx, old_func_index);
                let new_arg = _clone_subtree(ctx, old_arg_index);

                let app = DebruijnNode::app(new_func, new_arg);

                let app_index = ctx.tree.alloc(app);
                app_index
            }
        }
    }

    let mut context = Context {
        tree,
        old_abstraction_chain: vec![],
        new_abstraction_chain: vec![],
    };

    _clone_subtree(&mut context, index)
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

    fn compile(term: &str) -> FlatTree {
        FlatTree::from(&Debruijn::from_str(term).unwrap())
    }

    fn redex_at_root(tree: &FlatTree) -> RedexMut {
        RedexMut::try_get(tree, 0, EdgeWithParent::IntoRoot, tree.root).unwrap()
    }

    #[test]
    fn round_trip() {
        let original = Debruijn::from("(λ λ λ 3 1 (2 1)) ((λ λ 2) (λ λ λ 3 1 (2 1))) λ λ 2");
        let flat = FlatTree::from(&original);
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
        let flat = FlatTree::from(&original).normalized();
        let roundtripped = Debruijn::from(&flat);

        assert_eq!(
            original, roundtripped,
            "Expected {original}, got {roundtripped}",
        );
    }

    #[test]
    fn usage_zero() {
        let mut tree = compile("(λ 2) (λ 50)");

        let redex = redex_at_root(&tree);
        assert_eq!(redex.body_usage, 0);

        beta_reduce(&mut tree, redex);

        let expected = compile("1");

        let actual = Debruijn::from(&tree);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }

    #[test]
    fn usage_one() {
        let mut tree = compile("(λ 1) (λ 50)");

        let redex = redex_at_root(&tree);
        assert_eq!(redex.body_usage, 1);

        beta_reduce(&mut tree, redex);

        let expected = compile("λ 50");

        let actual = Debruijn::from(&tree);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }

    #[test]
    fn body_is_leaf() {
        let mut tree = compile("(λ 1) (1 2 3 4)");

        let redex = redex_at_root(&tree);
        assert_eq!(redex.body_usage, 1);

        beta_reduce(&mut tree, redex);

        let expected = compile("1 2 3 4");

        let actual = Debruijn::from(&tree);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }

    #[test]
    fn body_is_not_leaf() {
        let mut tree = compile("(λ λ 2) (1 2 3 4)");

        let redex = redex_at_root(&tree);
        assert_eq!(redex.body_usage, 1);

        beta_reduce(&mut tree, redex);

        let expected = compile("λ 2 3 4 5");

        let actual = Debruijn::from(&tree);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }

    #[test]
    fn usage_many() {
        let mut tree = compile("(λ 1 λ 2 λ 3 λ 4) 100");

        let redex = redex_at_root(&tree);
        assert_eq!(redex.body_usage, 4);

        beta_reduce(&mut tree, redex);

        let expected = compile("100 λ 101 λ 102 λ 103");

        let actual = Debruijn::from(&tree);
        let expected = Debruijn::from(&expected);
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }
}
