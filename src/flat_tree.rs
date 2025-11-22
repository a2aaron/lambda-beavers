use core::fmt;
use std::{
    collections::{HashMap, HashSet},
    fmt::{Binary, Display},
    hash::Hash,
    num::NonZeroU32,
    ops::{Index, IndexMut},
    str::FromStr,
    usize,
};

use crate::{debruijn::Debruijn, graphviz};

#[derive(Debug, Clone)]
pub struct FlatTree {
    pub backing: Vec<Node>,
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

    fn alloc_blank_var(&mut self) -> BoundVarIndex {
        let backing_index = BackingIndex::new(self.backing.len());
        let dummy = Node::dummy_var();
        self.backing.push(dummy);
        BoundVarIndex(backing_index)
    }

    // Allocate a dummy node and return the backing index to the dummy.
    // This dummy node should be set to something reasonable.
    fn alloc_blank_abs(&mut self) -> AbsIndex {
        let backing_index = BackingIndex::new(self.backing.len());
        let dummy = Node::dummy_abs();
        self.backing.push(dummy);
        AbsIndex(backing_index)
    }

    /// Allocate the given term onto the backing vector. The node is set to the node
    /// in the input `term`.
    /// The return value is the index to the newly allocated node.
    fn alloc(&mut self, term: Node) -> BackingIndex {
        let term_index = BackingIndex::new(self.backing.len());
        self.backing.push(term);
        term_index
    }

    fn alloc_app(&mut self, func: BackingIndex, arg: BackingIndex) -> BackingIndex {
        let app = Node::App(Application { func, arg });
        self.alloc(app)
    }

    fn alloc_bound_var(&mut self, bound_var: BoundVariable) -> BoundVarIndex {
        let node = Node::BoundVar(bound_var);
        let index = self.alloc(node);
        BoundVarIndex(index)
    }

    fn alloc_free_var(&mut self, free_var: FreeVariable) -> BackingIndex {
        let node = Node::FreeVar(free_var);
        self.alloc(node)
    }

    fn fixup_next(&mut self, prev: PrevIndex, this_var: BoundVarIndex) {
        match prev {
            PrevIndex::Var(var) => {
                let var = self.get_bound_var_mut(var);
                var.next = Some(this_var);
            }
            PrevIndex::Abs(abs) => {
                let abs = self.get_abs_mut(abs);
                abs.entrance = Some(this_var);
            }
        }
    }

    pub fn normalized(&self) -> FlatTree {
        struct Context<'a> {
            old_tree: &'a FlatTree,
            new_tree: &'a mut FlatTree,
            old_abs_chain: Vec<AbsIndex>,
            new_abs_chain: Vec<AbsIndex>,
            new_abs_contours: HashMap<AbsIndex, Vec<BoundVarIndex>>,
        }

        impl<'a> Context<'a> {
            fn push(&mut self, old_abs_index: AbsIndex, new_abs_index: AbsIndex) {
                self.old_abs_chain.push(old_abs_index);
                self.new_abs_chain.push(new_abs_index);
                self.new_abs_contours.insert(new_abs_index, vec![]);
            }

            fn pop(&mut self) {
                self.old_abs_chain.pop();
                self.new_abs_chain.pop();
            }

            fn old_to_new(&self, old_abs: AbsIndex) -> AbsIndex {
                let debruijn_depth = self
                    .old_abs_chain
                    .iter()
                    .position(|idx| *idx == old_abs)
                    .unwrap();

                let new_abs_index = self.new_abs_chain[debruijn_depth];
                new_abs_index
            }

            fn add_new_var(&mut self, new_abs: AbsIndex, new_var: BoundVarIndex) {
                self.new_abs_contours
                    .get_mut(&new_abs)
                    .unwrap()
                    .push(new_var)
            }

            fn get_prev_for_contour(&self, new_abs_idx: AbsIndex) -> PrevIndex {
                match self.new_abs_contours.get(&new_abs_idx) {
                    Some(contour) => match contour.last() {
                        Some(last_var) => PrevIndex::Var(*last_var),
                        None => PrevIndex::Abs(new_abs_idx),
                    },
                    None => unreachable!(),
                }
            }
        }

        fn _normalize(ctx: &mut Context, old_node_index: BackingIndex) -> BackingIndex {
            match &ctx.old_tree[old_node_index] {
                Node::FreeVar(free) => ctx.new_tree.alloc_free_var(*free),
                Node::BoundVar(old_var) => {
                    let old_abs_idx = ctx.old_tree.get_binding_abs(old_var);
                    let new_abs_idx = ctx.old_to_new(old_abs_idx);
                    let new_prev = ctx.get_prev_for_contour(new_abs_idx);

                    let new_var_index = ctx.new_tree.alloc_blank_var();
                    ctx.add_new_var(new_abs_idx, new_var_index);
                    ctx.new_tree.fixup_next(new_prev, new_var_index);

                    let new_var = ctx.new_tree.get_bound_var_mut(new_var_index);
                    new_var.prev = new_prev.into();

                    new_var_index.0
                }
                Node::Abs(abstraction) => {
                    let old_abs_index = AbsIndex(old_node_index);
                    let old_body_index = abstraction.body;

                    let new_abs_index = ctx.new_tree.alloc_blank_abs();

                    ctx.push(old_abs_index, new_abs_index);
                    let new_body = _normalize(ctx, old_body_index);
                    ctx.pop();

                    let abs = ctx.new_tree.get_abs_mut(new_abs_index);
                    abs.body = new_body;

                    new_abs_index.0
                }
                Node::App(application) => {
                    let old_func_index = application.func;
                    let old_arg_index = application.arg;

                    let new_func = _normalize(ctx, old_func_index);
                    let new_arg = _normalize(ctx, old_arg_index);
                    ctx.new_tree.alloc_app(new_func, new_arg)
                }
            }
        }

        let mut new_tree = FlatTree::new();

        let mut ctx = Context {
            old_tree: self,
            new_tree: &mut new_tree,
            old_abs_chain: vec![],
            new_abs_chain: vec![],
            new_abs_contours: HashMap::new(),
        };

        let root_node = _normalize(&mut ctx, self.root);
        new_tree.root = root_node;
        new_tree
    }

    fn get_abs(&self, abs: AbsIndex) -> Abstraction {
        match &self[abs.0] {
            Node::Abs(abs) => abs.clone(),
            node => panic!("Expected abstraction for term @ {abs}, got {node:?}",),
        }
    }

    fn get_abs_mut(&mut self, abs: AbsIndex) -> &mut Abstraction {
        match &mut self[abs.0] {
            Node::Abs(abs) => abs,
            node => panic!("Expected abstraction for term @ {abs}, got {node:?}"),
        }
    }

    fn get_app_mut(&mut self, app: BackingIndex) -> &mut Application {
        match &mut self[app] {
            Node::App(app) => app,
            node => panic!("Expected abstraction for term @ {app}, got {node:?}",),
        }
    }

    fn get_bound_var(&self, var: BoundVarIndex) -> &BoundVariable {
        match &self[var.0] {
            Node::BoundVar(var) => var,
            node => panic!("Expected variable for term @ {var}, got {node:?}",),
        }
    }

    fn get_bound_var_mut(&mut self, var: BoundVarIndex) -> &mut BoundVariable {
        match &mut self[var.0] {
            Node::BoundVar(var) => var,
            node => panic!("Expected variable for term @ {var}, got {node:?}",),
        }
    }

    fn get_binding_abs<'a>(&'a self, mut bound_var: &'a BoundVariable) -> AbsIndex {
        loop {
            match bound_var.prev(self) {
                PrevIndex::Var(bound_var_index) => {
                    let prev_var = self.get_bound_var(bound_var_index);
                    bound_var = prev_var;
                }
                PrevIndex::Abs(abs_index) => return abs_index,
            }
        }
    }

    pub fn check_contours(&self) -> ContourResult<()> {
        struct Context<'a> {
            tree: &'a FlatTree,
            contours: HashMap<AbsIndex, Vec<BoundVarIndex>>,
            non_garbage: HashSet<BackingIndex>,
        }

        impl<'a> Context<'a> {
            fn check_prev_index(&self, prev: BackingIndex) -> ContourResult<PrevIndex> {
                match &self.tree[prev] {
                    Node::BoundVar(_) => Ok(PrevIndex::Var(BoundVarIndex(prev))),
                    Node::Abs(_) => Ok(PrevIndex::Abs(AbsIndex(prev))),
                    node => Err(ContourError::ExpectedAbsOrBoundVar {
                        index: prev,
                        actual: node.clone(),
                    }),
                }
            }

            fn check_abs_index(&self, index: AbsIndex) -> ContourResult<&'a Abstraction> {
                match &self.tree[index.0] {
                    Node::Abs(abstraction) => ContourResult::Ok(abstraction),
                    node => ContourResult::Err(ContourError::ExpectedAbs {
                        index: index,
                        actual: node.clone(),
                    }),
                }
            }

            fn check_bound_var_index(
                &self,
                index: BoundVarIndex,
            ) -> ContourResult<&'a BoundVariable> {
                match &self.tree[index.0] {
                    Node::BoundVar(bound_variable) => ContourResult::Ok(bound_variable),
                    node => ContourResult::Err(ContourError::ExpectedBoundVar {
                        index,
                        actual: node.clone(),
                    }),
                }
            }

            fn check_contour(&mut self, abs: &Abstraction, abs_idx: AbsIndex) -> ContourResult<()> {
                let mut contour = vec![];

                if let Some(entrance) = abs.entrance {
                    let node1 = self.check_bound_var_index(entrance)?;
                    let prev_of_node1 = self.check_prev_index(node1.prev)?;
                    if prev_of_node1 != PrevIndex::Abs(abs_idx) {
                        return Err(ContourError::PrevEntranceMismatch {
                            abs: abs_idx,
                            entrance_of_abs: entrance,
                            entrance,
                            prev_of_entrance: node1.prev(self.tree),
                        });
                    }

                    let mut node1_idx = entrance;
                    // We expect that each node in the contour has next and prev nodes that properly
                    // match up.
                    loop {
                        contour.push(node1_idx);
                        let node1 = self.check_bound_var_index(node1_idx)?;
                        if let Some(next_of_node1) = node1.next {
                            let node2 = self.check_bound_var_index(next_of_node1)?;

                            let prev_of_node2 = self.check_prev_index(node2.prev)?;
                            if prev_of_node2 != PrevIndex::Var(node1_idx) {
                                return Err(ContourError::PrevNextMismatch {
                                    node1: node1_idx,
                                    next_of_node1,
                                    prev_of_node2,
                                });
                            }

                            node1_idx = next_of_node1;
                        } else {
                            break;
                        }
                    }
                } else {
                    // No contour--so nothing to check
                    // (However, we do later check that bound variables do not lead back to this abstrction)
                }

                let expect_none = self.contours.insert(abs_idx, contour);
                assert!(expect_none.is_none());
                Ok(())
            }

            fn check_bound_var_for_loop(&self, bound_var: BoundVarIndex) -> ContourResult<()> {
                // We expect this to be a non-looping linked list

                // Check backwards
                let mut contour_backwards = vec![];
                let mut this_var = bound_var;
                let abs_index = loop {
                    let bound_var = self.check_bound_var_index(this_var)?;
                    let prev = self.check_prev_index(bound_var.prev)?;
                    match prev {
                        PrevIndex::Var(prev) => {
                            if contour_backwards.contains(&prev) {
                                return Err(ContourError::LoopDetectedFromPrev {
                                    node: this_var,
                                    prev,
                                });
                            }
                            contour_backwards.push(prev);
                            this_var = prev;
                        }
                        PrevIndex::Abs(abs_index) => break abs_index,
                    }
                };

                let mut contour_forwards = vec![];
                let mut this_var = bound_var;
                loop {
                    let bound_var = self.check_bound_var_index(this_var)?;
                    match bound_var.next {
                        Some(next) => {
                            if contour_forwards.contains(&next) {
                                return Err(ContourError::LoopDetectedFromNext {
                                    node: this_var,
                                    next,
                                });
                            }
                            contour_forwards.push(next);
                            this_var = next;
                        }
                        None => break,
                    }
                }

                let mut contour = vec![];

                contour_backwards.reverse();
                contour.extend(contour_backwards);
                contour.push(bound_var);
                contour.extend(contour_forwards);

                let abs = self.check_abs_index(abs_index)?;
                if abs.entrance.is_none() {
                    return Err(ContourError::AbsIsNoneButHasBoundVars {
                        abs: abs_index,
                        contour,
                    });
                }

                Ok(())
            }

            fn mark_not_garbage(&mut self, node: BackingIndex) {
                self.non_garbage.insert(node);
            }
        }

        fn _check_contours(ctx: &mut Context, node: BackingIndex) -> ContourResult<()> {
            ctx.mark_not_garbage(node);
            match &ctx.tree[node] {
                Node::FreeVar(_) => Ok(()),
                Node::BoundVar(_) => ctx.check_bound_var_for_loop(BoundVarIndex(node)),
                Node::Abs(abstraction) => {
                    ctx.check_contour(abstraction, AbsIndex(node))?;
                    _check_contours(ctx, abstraction.body)
                }
                Node::App(application) => {
                    _check_contours(ctx, application.func)?;
                    _check_contours(ctx, application.arg)
                }
            }
        }

        let mut ctx = Context {
            tree: self,
            contours: HashMap::new(),
            non_garbage: HashSet::new(),
        };
        _check_contours(&mut ctx, self.root)?;
        Ok(())
    }
}

pub type ContourResult<T> = Result<T, ContourError>;

#[derive(Debug)]
pub enum ContourError {
    ExpectedBoundVar {
        index: BoundVarIndex,
        actual: Node,
    },
    ExpectedAbs {
        index: AbsIndex,
        actual: Node,
    },
    ExpectedAbsOrBoundVar {
        index: BackingIndex,
        actual: Node,
    },
    AbsIsNoneButHasBoundVars {
        abs: AbsIndex,
        contour: Vec<BoundVarIndex>,
    },
    PrevEntranceMismatch {
        abs: AbsIndex,
        entrance_of_abs: BoundVarIndex,
        entrance: BoundVarIndex,
        prev_of_entrance: PrevIndex,
    },
    PrevNextMismatch {
        node1: BoundVarIndex,
        next_of_node1: BoundVarIndex,
        prev_of_node2: PrevIndex,
    },
    LoopDetectedFromPrev {
        node: BoundVarIndex,
        prev: BoundVarIndex,
    },
    LoopDetectedFromNext {
        node: BoundVarIndex,
        next: BoundVarIndex,
    },
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
    type Output = Node;

    fn index(&self, index: BackingIndex) -> &Self::Output {
        &self.backing[index.0 as usize]
    }
}

impl IndexMut<BackingIndex> for FlatTree {
    fn index_mut(&mut self, index: BackingIndex) -> &mut Self::Output {
        &mut self.backing[index.0 as usize]
    }
}

impl From<Vec<Node>> for FlatTree {
    fn from(backing: Vec<Node>) -> Self {
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
        struct Context<'a> {
            tree: &'a mut FlatTree,
            abs_chain: Vec<(AbsIndex, PrevIndex)>,
        }

        impl<'a> Context<'a> {
            fn push(&mut self, abs: AbsIndex) {
                let prev = PrevIndex::Abs(abs);
                self.abs_chain.push((abs, prev))
            }

            fn pop(&mut self) {
                self.abs_chain.pop();
            }

            fn alloc_var_and_fixup(&mut self, debruijn_index: usize) -> BackingIndex {
                if debruijn_index > self.abs_chain.len() {
                    let free_height = debruijn_index - self.abs_chain.len();
                    let height = NonZeroU32::new(free_height as u32).unwrap();
                    let var = FreeVariable { height };
                    self.tree.alloc_free_var(var)
                } else {
                    let chain_index = self.abs_chain.len() - debruijn_index;
                    let (_, prev) = &mut self.abs_chain[chain_index];

                    let this_var = BoundVariable {
                        prev: (*prev).into(),
                        next: None,
                    };
                    let this_var_index = self.tree.alloc_bound_var(this_var);

                    self.tree.fixup_next(*prev, this_var_index);

                    *prev = PrevIndex::Var(this_var_index);

                    this_var_index.0
                }
            }
        }

        fn flatten(ctx: &mut Context, term: &Debruijn) -> BackingIndex {
            match term {
                Debruijn::Index(debruijn_index) => ctx.alloc_var_and_fixup(*debruijn_index),
                Debruijn::Abstraction { body } => {
                    // Pre-allocation is needed here so that we can have a spot for the abstraction
                    // node to reside in. We will need this value to be allocated by the time we
                    // go to compute the binding for any variable nodes that depend on it.
                    let abs_index = ctx.tree.alloc_blank_abs();

                    ctx.push(abs_index);
                    let body = flatten(ctx, body);
                    ctx.pop();

                    let abs = ctx.tree.get_abs_mut(abs_index);
                    abs.body = body;

                    abs_index.0
                }
                Debruijn::Application { func, arg } => {
                    let func = flatten(ctx, func);
                    let arg = flatten(ctx, arg);
                    ctx.tree.alloc_app(func, arg)
                }
            }
        }

        let mut tree = FlatTree::new();
        let mut ctx = Context {
            tree: &mut tree,
            abs_chain: vec![],
        };
        let root_index = flatten(&mut ctx, term);
        tree.root = root_index;
        tree
    }
}

pub fn compute_debruijn_index_free(abs_chain: &[AbsIndex], free_var: &FreeVariable) -> usize {
    let debruijn_depth = abs_chain.len();
    debruijn_depth + free_var.height.get() as usize
}

pub fn compute_debruijn_index_bound(
    tree: &FlatTree,
    chain: &[AbsIndex],
    bound_var: &BoundVariable,
) -> usize {
    let abs = tree.get_binding_abs(bound_var);
    let index = chain.iter().position(|abs_idx| *abs_idx == abs).unwrap();
    let debruijn_depth = chain.len();
    let debruijn_index = debruijn_depth - index;
    debruijn_index
}

impl From<&FlatTree> for Debruijn {
    fn from(tree: &FlatTree) -> Self {
        struct Context<'a> {
            tree: &'a FlatTree,
            chain: Vec<AbsIndex>,
        }
        impl<'a> Context<'a> {
            fn push(&mut self, abs: AbsIndex) {
                self.chain.push(abs);
            }

            fn pop(&mut self) {
                self.chain.pop();
            }

            fn compute_debruijn_index(&self, bound_var: &BoundVariable) -> usize {
                compute_debruijn_index_bound(self.tree, &self.chain, bound_var)
            }
        }
        fn _from(ctx: &mut Context, index: BackingIndex) -> Debruijn {
            match &ctx.tree[index] {
                Node::FreeVar(free_var) => {
                    let index = compute_debruijn_index_free(&ctx.chain, free_var);
                    Debruijn::Index(index)
                }
                Node::BoundVar(bound_var) => {
                    let debruijn_index = ctx.compute_debruijn_index(bound_var);
                    Debruijn::Index(debruijn_index)
                }
                Node::Abs(abstraction) => {
                    let abs = AbsIndex(index);
                    ctx.push(abs);
                    let body = _from(ctx, abstraction.body);
                    ctx.pop();
                    Debruijn::Abstraction {
                        body: Box::new(body),
                    }
                }
                Node::App(application) => {
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
            chain: vec![],
        };
        _from(&mut ctx, tree.root)
    }
}

// The depth relative to some term. This is used to determine if a variable is free within a term
// If a given Index node has a DebruijnIndex >= DebruijnDepth, then that Index node is a free variable
// with respect to that subtree)
// Zero indicates that there are no abstractions between the two terms, one indicates one abstraction, etc
pub type DebruijnDepth = usize;

// The number of times a variable is used in an abstraction.
pub type Usage = u32;

/// A pointer to a given DebruijnNode within a FlatTree
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BackingIndex(u32);
impl BackingIndex {
    pub const DUMMY: BackingIndex = BackingIndex(u32::MAX);

    pub fn new(index: usize) -> Self {
        Self(index as _)
    }

    pub fn get(&self) -> usize {
        self.0 as usize
    }
}

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
#[derive(Debug, Clone, Copy)]
pub enum ParentEdge {
    /// The "edge" has no parent, and the child here is the root of the tree
    IntoRoot,
    /// The edge is an abstraction to body edge, and the BackingIndex here is the index for the abstraction
    AbsToBody(AbsIndex),
    /// The edge is an application to function edge, and the BackingIndex here is the index for the application
    AppToFunc(BackingIndex),
    /// The edge is an application to argument edge, and the BackingIndex here is the index for the application
    AppToArg(BackingIndex),
}
impl ParentEdge {
    pub fn backing_index(&self) -> Option<BackingIndex> {
        match self {
            ParentEdge::IntoRoot => None,
            ParentEdge::AbsToBody(abs) => Some(abs.0),
            ParentEdge::AppToFunc(app) => Some(*app),
            ParentEdge::AppToArg(app) => Some(*app),
        }
    }
}

// Helper type -- the BackingIndex within this struct must point to a Node::Var
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundVarIndex(pub BackingIndex);
impl Display for BoundVarIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

// Helper type -- the BackingIndex within this struct must point to a Node::Abs
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbsIndex(pub BackingIndex);
impl Display for AbsIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrevIndex {
    Var(BoundVarIndex),
    Abs(AbsIndex),
}

impl From<PrevIndex> for BackingIndex {
    fn from(value: PrevIndex) -> Self {
        match value {
            PrevIndex::Var(var) => var.0,
            PrevIndex::Abs(abs) => abs.0,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Abstraction {
    // The index of the body of the abstraction
    pub body: BackingIndex,
    // The head of the "contour" linked list. Each variable node in the linked list binds to this
    // abstraction node and links to their neighbors in a doubly-linked list. The node that is pointed
    // to by this field additionally points back to this abstraction node (making this abstraction node
    // as the head of the linked list)
    // If this is none, then this abstraction has no usages.
    pub entrance: Option<BoundVarIndex>,
}

#[derive(Clone, Copy)]
pub struct Application {
    pub func: BackingIndex,
    pub arg: BackingIndex,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct FreeVariable {
    // The number of abstractions above the root that this Index node binds to
    // For example, in λ x, if x = 2, then we have a free bind of 1
    // If x = 3, then we have a free bind of 2, and so on.
    // Zero is not a valid value for this because we start 1-indexed
    // Note that this is NOT a debruijn index, it's a debruijn depth, as it always refers
    // to a constant number of abstractions above the root, no matter how deeply nested the
    // actual index is
    height: NonZeroU32,
}

impl Display for FreeVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "free ({})", self.height)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BoundVariable {
    pub prev: BackingIndex,
    pub next: Option<BoundVarIndex>,
}

impl Display for BoundVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let prev = self.prev;
        match self.next {
            Some(next) => write!(f, "prev: {prev} -> next: {next}"),
            None => write!(f, "prev: {prev}"),
        }
    }
}

impl BoundVariable {
    fn prev(&self, tree: &FlatTree) -> PrevIndex {
        match &tree[self.prev] {
            Node::BoundVar(_) => PrevIndex::Var(BoundVarIndex(self.prev)),
            Node::Abs(_) => PrevIndex::Abs(AbsIndex(self.prev)),
            node => panic!(
                "Expected bound variable or abstraction at {}, got {node:?}",
                self.prev
            ),
        }
    }
}

#[derive(Clone)]
pub enum Node {
    // This backing index points to the abstraction that this index binds to
    FreeVar(FreeVariable),
    BoundVar(BoundVariable),
    Abs(Abstraction),
    App(Application),
}
impl Node {
    fn dummy_abs() -> Node {
        let abs = Abstraction {
            body: BackingIndex::DUMMY,
            entrance: None,
        };
        Node::Abs(abs)
    }

    fn dummy_var() -> Node {
        let var = BoundVariable {
            prev: BackingIndex::DUMMY,
            next: None,
        };
        Node::BoundVar(var)
    }
}

impl From<Abstraction> for Node {
    fn from(abs: Abstraction) -> Self {
        Node::Abs(abs)
    }
}

impl From<Application> for Node {
    fn from(app: Application) -> Self {
        Node::App(app)
    }
}

impl std::fmt::Debug for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FreeVar(free_var) => write!(f, "var: {free_var}"),
            Self::BoundVar(bound_var) => write!(f, "var: {bound_var}"),
            Self::Abs(abs) => match abs.entrance {
                Some(entrance) => write!(f, "abs: body -> {} (entrance -> {})", abs.body, entrance),
                None => write!(f, "abs: body -> {}", abs.body),
            },
            Self::App(app) => write!(f, "app: func -> {}, arg -> {}", app.func, app.arg),
        }
    }
}

#[derive(Debug, Clone)]
pub struct RedexMut {
    // The number of abstractions in the parent chain above this redex
    pub debruijn_depth: DebruijnDepth,

    pub parent_to_app: ParentEdge,
    // The index of the redex application node
    pub app_index: BackingIndex,
    // The left child of the redex's application node. This should be an abstraction node
    pub func_index: AbsIndex,
    // The child of the left child of the redex application
    body_index: BackingIndex,
    // The right child of the redex's application node.
    pub arg_index: BackingIndex,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum BodyUsage {
    Zero,
    One,
    Many,
}

impl RedexMut {
    fn body_usage(&self, tree: &FlatTree) -> BodyUsage {
        let abs = tree.get_abs(self.func_index);
        match abs.entrance {
            Some(entrance) => {
                let var = tree.get_bound_var(entrance);
                match var.next {
                    Some(_) => BodyUsage::Many,
                    None => BodyUsage::One,
                }
            }
            None => BodyUsage::Zero,
        }
    }

    pub fn is_redex(tree: &FlatTree, term: BackingIndex) -> bool {
        match tree[term] {
            Node::App(app) => match tree[app.func] {
                Node::Abs { .. } => true,
                _ => false,
            },
            _ => false,
        }
    }

    pub fn try_get(
        tree: &FlatTree,
        debruijn_depth: DebruijnDepth,
        parent_to_app: ParentEdge,
        app_index: BackingIndex,
    ) -> Option<RedexMut> {
        match tree[app_index] {
            Node::App(app) => match &tree[app.func] {
                Node::Abs(abs) => {
                    let func_index = AbsIndex(app.func);
                    let redex = RedexMut {
                        debruijn_depth,
                        parent_to_app,
                        app_index,
                        func_index,
                        body_index: abs.body,
                        arg_index: app.arg,
                    };
                    Some(redex)
                }
                _ => None,
            },
            _ => None,
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

        fn _get_redexes(ctx: &mut Context, index: BackingIndex, parent_to_current: ParentEdge) {
            match &ctx.tree[index] {
                Node::FreeVar(_) => (),
                Node::BoundVar(_) => (),
                Node::Abs(abstraction) => {
                    let index = AbsIndex(index);
                    ctx.debruijn_depth += 1;
                    _get_redexes(ctx, abstraction.body, ParentEdge::AbsToBody(index));
                    ctx.debruijn_depth -= 1;
                }
                Node::App(application) => {
                    if let Some(redex) =
                        RedexMut::try_get(ctx.tree, ctx.debruijn_depth, parent_to_current, index)
                    {
                        ctx.redexes.push(redex);
                    }
                    _get_redexes(ctx, application.func, ParentEdge::AppToFunc(index));
                    _get_redexes(ctx, application.arg, ParentEdge::AppToArg(index));
                }
            }
        }

        let mut ctx = Context {
            tree: self,
            debruijn_depth: 0,
            redexes: vec![],
        };
        _get_redexes(&mut ctx, self.root, ParentEdge::IntoRoot);
        ctx.redexes
    }

    pub fn is_bnf(&self) -> bool {
        fn _is_bnf(tree: &FlatTree, index: BackingIndex) -> bool {
            match &tree[index] {
                Node::FreeVar(_) => false,
                Node::BoundVar(_) => false,
                Node::Abs(abstraction) => _is_bnf(tree, abstraction.body),
                Node::App(application) => {
                    !RedexMut::is_redex(tree, index)
                        && _is_bnf(tree, application.func)
                        && _is_bnf(tree, application.arg)
                }
            }
        }

        _is_bnf(self, self.root)
    }
}

pub fn beta_reduce(tree: &mut FlatTree, redex: &RedexMut) -> BackingIndex {
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

    // This is the following tree fragment
    // --> new_body
    // (the parent to this edge is supposed to be abs, although this will change later in this methods)
    // Note that body may have been re-allocated--this happens when the body consists of a single
    // leaf node that gets substituted--aka: the abstraction node looks like λ 1
    let new_body = substitute(tree, &redex);

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
    new_body
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
fn repoint_node(tree: &mut FlatTree, parent: ParentEdge, child: BackingIndex) {
    if parent.backing_index() == Some(child) {
        graphviz::debug_write_to_file(tree, "bad_repoint");
        panic!("attempt to repoint {parent:?} to {child} which would cause a loop (tree: {tree:?}");
    }
    match parent {
        ParentEdge::AbsToBody(parent) => {
            let abs = tree.get_abs_mut(parent);
            abs.body = child;
        }
        ParentEdge::AppToFunc(parent) => {
            let app = tree.get_app_mut(parent);
            app.func = child;
        }
        ParentEdge::AppToArg(parent) => {
            let app = tree.get_app_mut(parent);
            app.arg = child;
        }
        ParentEdge::IntoRoot => tree.root = child,
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
fn substitute(tree: &mut FlatTree, redex: &RedexMut) -> BackingIndex {
    if redex.body_usage(tree) == BodyUsage::Zero {
        // THIS IS GOING TO BLOW UP IMMEDIATELY!!!!!!!!!!!!!!
        // Anything which has zero usage requires that we walk the arg subtree to remove BoundVars
        // from their contours. Which is hugely annoying

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

fn substitute_nonzero_usage(tree: &mut FlatTree, redex: &RedexMut) {
    struct Context<'a> {
        tree: &'a mut FlatTree,
        func_index: AbsIndex,
        arg_index: BackingIndex,
    }

    fn _substitute(ctx: &mut Context, node_index: BackingIndex, parent_to_node: ParentEdge) {
        match &ctx.tree[node_index] {
            Node::FreeVar(_) => (), // Free variable will never be substituted
            Node::BoundVar(bound_var) => {
                let is_substituting = ctx.tree.get_binding_abs(bound_var) == ctx.func_index;
                if is_substituting {
                    // Optimization opportunity: Instead of making `arg` become garbage, instead reuse it and avoid doing one alloc.
                    let last_arg_allocation = bound_var.next.is_none();
                    let new_child = if last_arg_allocation {
                        ctx.arg_index
                    } else {
                        clone_subtree(ctx.tree, ctx.arg_index)
                    };

                    // Point parent to the newly created subtree
                    repoint_node(ctx.tree, parent_to_node, new_child);
                }
            }
            Node::Abs(abstraction) => {
                let abs = AbsIndex(node_index);
                _substitute(ctx, abstraction.body, ParentEdge::AbsToBody(abs))
            }
            Node::App(application) => {
                let func = application.func;
                let arg = application.arg;

                _substitute(ctx, func, ParentEdge::AppToFunc(node_index));
                _substitute(ctx, arg, ParentEdge::AppToArg(node_index));
            }
        }
    }

    let mut ctx = Context {
        tree,
        func_index: redex.func_index,
        arg_index: redex.arg_index,
    };

    _substitute(
        &mut ctx,
        redex.body_index,
        ParentEdge::AbsToBody(redex.func_index),
    );
}

struct CloneContext {
    old_to_new: Vec<(AbsIndex, AbsIndex)>,
}
impl CloneContext {
    fn new() -> CloneContext {
        CloneContext {
            old_to_new: Vec::with_capacity(64),
        }
    }

    fn push(&mut self, old_abs: AbsIndex, new_abs: AbsIndex) {
        self.old_to_new.push((old_abs, new_abs));
    }

    fn pop(&mut self) {
        self.old_to_new.pop();
    }

    fn get_new_abs(&self, old_abs: AbsIndex) -> Option<AbsIndex> {
        self.old_to_new.iter().find_map(|pair| {
            if pair.0 == old_abs {
                Some(pair.1)
            } else {
                None
            }
        })
    }
}

/// Clone the given subtree.
///
/// MEMORY: Allocates new subtree, returned value is the newly allocated tree
fn clone_subtree(tree: &mut FlatTree, index: BackingIndex) -> BackingIndex {
    fn _clone_subtree(
        tree: &mut FlatTree,
        ctx: &mut CloneContext,
        old_node_index: BackingIndex,
    ) -> BackingIndex {
        match &tree[old_node_index] {
            Node::FreeVar(free_var) => {
                let node = Node::FreeVar(*free_var);
                tree.alloc(node)
            }
            Node::BoundVar(variable) => {
                let old_abs = tree.get_binding_abs(variable);

                let new_var = tree.alloc_blank_var();
                if let Some(new_abs) = ctx.get_new_abs(old_abs) {
                    // If this is some, then the variable is bound within the subtree being cloned
                    // In this case, the variable needs to point to the new abstraction's contour
                    insert_into_contour(tree, new_abs, new_var);
                } else {
                    // Otherwise, the variable is bound within the tree but outside of the subtree bieng cloned.
                    // In that case, it will be inserted into the existing contour
                    insert_into_contour(tree, old_abs, new_var);
                }

                new_var.0
            }
            Node::Abs(abstraction) => {
                let old_body_index = abstraction.body;

                let new_abs_index = tree.alloc_blank_abs();

                let old_abs = AbsIndex(old_node_index);
                ctx.push(old_abs, new_abs_index);
                let new_body = _clone_subtree(tree, ctx, old_body_index);
                ctx.pop();

                let new_abs = tree.get_abs_mut(new_abs_index);
                new_abs.body = new_body;

                new_abs_index.0
            }
            Node::App(application) => {
                let old_func_index = application.func;
                let old_arg_index = application.arg;

                let new_func = _clone_subtree(tree, ctx, old_func_index);
                let new_arg = _clone_subtree(tree, ctx, old_arg_index);

                let app_index = tree.alloc_app(new_func, new_arg);
                app_index
            }
        }
    }
    let mut ctx = CloneContext::new();
    _clone_subtree(tree, &mut ctx, index)
}

fn insert_into_contour(tree: &mut FlatTree, abs_index: AbsIndex, var_index: BoundVarIndex) {
    let abs = tree.get_abs_mut(abs_index);

    match abs.entrance {
        Some(entrance) => {
            abs.entrance = Some(var_index);

            let entrance_var = tree.get_bound_var_mut(entrance);
            entrance_var.prev = var_index.0;

            let var = tree.get_bound_var_mut(var_index);
            var.next = Some(entrance);
            var.prev = abs_index.0;
        }
        None => {
            abs.entrance = Some(var_index);

            let var = tree.get_bound_var_mut(var_index);
            var.next = None;
            var.prev = abs_index.0;
        }
    }
}

#[cfg(test)]
mod test {
    macro_rules! mario {
        () => {
            use super::*;
        };
    }

    mario!();
    use crate::debruijn::Debruijn;

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
}
