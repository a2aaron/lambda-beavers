use core::fmt;
use std::{
    collections::{HashMap, HashSet},
    fmt::{Binary, Display},
    hash::Hash,
    num::NonZeroU32,
    str::FromStr,
    usize,
};

use crate::debruijn::Debruijn;

// The depth relative to some term. This is used to determine if a variable is free within a term
// If a given Index node has a DebruijnIndex >= DebruijnDepth, then that Index node is a free variable
// with respect to that subtree)
// Zero indicates that there are no abstractions between the two terms, one indicates one abstraction, etc
pub type DebruijnDepth = usize;

#[derive(Debug, Clone)]
pub struct FlatTree {
    pub backing: Vec<Node>,
    // The into-root edge, which has no parent and whose child is the root node itself
    // --> root
    pub root: BackingIndex,
    pub garbage_count: usize,
}
impl FlatTree {
    pub fn new() -> FlatTree {
        FlatTree::with_capacity(0)
    }

    fn with_capacity(capacity: usize) -> FlatTree {
        FlatTree {
            backing: Vec::with_capacity(capacity),
            root: BackingIndex(0),
            garbage_count: 0,
        }
    }

    pub fn total_count(&self) -> usize {
        self.backing.len()
    }

    pub fn alive_count(&self) -> usize {
        self.total_count() - self.garbage_count
    }

    pub fn get(&self, index: BackingIndex) -> &Node {
        &self.backing[index.0 as usize]
    }

    pub fn get_mut(&mut self, index: BackingIndex) -> &mut Node {
        &mut self.backing[index.0 as usize]
    }

    pub fn get_ref(&'_ self, index: BackingIndex) -> NodeRef<'_> {
        match &self.backing[index.0 as usize] {
            Node::FreeVar(free_variable) => NodeRef::FreeVar(free_variable, FreeVarIndex(index)),
            Node::BoundVar(bound_variable) => {
                NodeRef::BoundVar(bound_variable, BoundVarIndex(index))
            }
            Node::Abs(abstraction) => NodeRef::Abs(abstraction, AbsIndex(index)),
            Node::App(application) => NodeRef::App(application, AppIndex(index)),
        }
    }

    pub fn get_ref_mut(&'_ mut self, index: BackingIndex) -> NodeRefMut<'_> {
        match &mut self.backing[index.0 as usize] {
            Node::FreeVar(free_variable) => NodeRefMut::FreeVar(free_variable, FreeVarIndex(index)),
            Node::BoundVar(bound_variable) => {
                NodeRefMut::BoundVar(bound_variable, BoundVarIndex(index))
            }
            Node::Abs(abstraction) => NodeRefMut::Abs(abstraction, AbsIndex(index)),
            Node::App(application) => NodeRefMut::App(application, AppIndex(index)),
        }
    }

    pub fn get_bound_var(&self, var: BoundVarIndex) -> &BoundVariable {
        match self.get(var.0) {
            Node::BoundVar(var) => var,
            node => panic!("Expected variable for term @ {var}, got {node:?}",),
        }
    }

    pub fn get_bound_var_mut(&mut self, var: BoundVarIndex) -> &mut BoundVariable {
        match self.get_mut(var.0) {
            Node::BoundVar(var) => var,
            node => panic!("Expected variable for term @ {var}, got {node:?}",),
        }
    }

    pub fn get_abs(&self, abs: AbsIndex) -> &Abstraction {
        match self.get(abs.0) {
            Node::Abs(abs) => abs,
            node => panic!("Expected abstraction for term @ {abs}, got {node:?}",),
        }
    }

    pub fn get_abs_mut(&mut self, abs: AbsIndex) -> &mut Abstraction {
        match self.get_mut(abs.0) {
            Node::Abs(abs) => abs,
            node => panic!("Expected abstraction for term @ {abs}, got {node:?}"),
        }
    }

    pub fn get_app(&self, app: AppIndex) -> &Application {
        match self.get(app.0) {
            Node::App(app) => app,
            node => panic!("Expected abstraction for term @ {app}, got {node:?}",),
        }
    }

    pub fn get_app_mut(&mut self, app: AppIndex) -> &mut Application {
        match self.get_mut(app.0) {
            Node::App(app) => app,
            node => panic!("Expected abstraction for term @ {app}, got {node:?}",),
        }
    }

    /// Allocate the given term onto the backing vector. The node is set to the node in the input `term`.
    /// The return value is the index to the newly allocated node.
    pub fn alloc(&mut self, term: Node) -> BackingIndex {
        let term_index = BackingIndex::new(self.backing.len());
        self.backing.push(term);
        term_index
    }

    pub fn alloc_bound_var(&mut self, bound_var: BoundVariable) -> BoundVarIndex {
        let node = Node::BoundVar(bound_var);
        let index = self.alloc(node);
        BoundVarIndex(index)
    }

    pub fn alloc_free_var(&mut self, free_var: FreeVariable) -> BackingIndex {
        let node = Node::FreeVar(free_var);
        self.alloc(node)
    }

    pub fn alloc_app(&mut self, func: BackingIndex, arg: BackingIndex) -> BackingIndex {
        let app = Node::App(Application { func, arg });
        self.alloc(app)
    }

    // Allocate a dummy BoundVar and return the BoundVarIndex to the dummy.
    // This dummy node should be set to something reasonable.
    pub fn alloc_blank_var(&mut self, parent: ParentEdge) -> BoundVarIndex {
        let backing_index = BackingIndex::new(self.backing.len());

        let var = BoundVariable {
            prev: BackingIndex::DUMMY,
            next: None,
            parent,
        };

        let dummy = Node::BoundVar(var);
        self.backing.push(dummy);
        BoundVarIndex(backing_index)
    }

    // Allocate a dummy Abstraction and return the AbsIndex to the dummy.
    // This dummy node should be set to something reasonable.
    pub fn alloc_blank_abs(&mut self) -> AbsIndex {
        let backing_index = BackingIndex::new(self.backing.len());
        let abs = Abstraction {
            body: BackingIndex::DUMMY,
            entrance: None,
        };
        let dummy = Node::Abs(abs);
        self.backing.push(dummy);
        AbsIndex(backing_index)
    }

    pub fn alloc_blank_app(&mut self) -> AppIndex {
        let backing_index = BackingIndex::new(self.backing.len());

        let app = Application {
            func: BackingIndex::DUMMY,
            arg: BackingIndex::DUMMY,
        };
        let dummy = Node::App(app);
        self.backing.push(dummy);
        AppIndex(backing_index)
    }

    /// Given a bound variable, returns AbsIndex of the abstraction that the bound variable binds to
    pub fn get_binding_abs<'a>(&'a self, mut bound_var: &'a BoundVariable) -> AbsIndex {
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

    // Fix up a contour so that "this_var" is inserted between prev and next
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

impl From<&Debruijn> for FlatTree {
    fn from(term: &Debruijn) -> Self {
        flatten(term)
    }
}

impl From<&FlatTree> for Debruijn {
    fn from(tree: &FlatTree) -> Self {
        unflatten(tree)
    }
}

/// ####################
/// # NODE AND NODEREF #
/// ####################

#[derive(Clone)]
pub enum Node {
    // This backing index points to the abstraction that this index binds to
    FreeVar(FreeVariable),
    BoundVar(BoundVariable),
    Abs(Abstraction),
    App(Application),
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

/// Helper enum for working with both a node reference and it's typed BackingIndex
pub enum NodeRef<'a> {
    BoundVar(&'a BoundVariable, BoundVarIndex),
    FreeVar(&'a FreeVariable, FreeVarIndex),
    Abs(&'a Abstraction, AbsIndex),
    App(&'a Application, AppIndex),
}
impl<'a> NodeRef<'a> {
    fn clone_node(&self) -> Node {
        match *self {
            NodeRef::BoundVar(bound_variable, _) => Node::BoundVar(bound_variable.clone()),
            NodeRef::FreeVar(free_variable, _) => Node::FreeVar(free_variable.clone()),
            NodeRef::Abs(abstraction, _) => Node::Abs(abstraction.clone()),
            NodeRef::App(application, _) => Node::App(application.clone()),
        }
    }
}

/// Helper enum for working with both a mutable node reference and it's typed BackingIndex
pub enum NodeRefMut<'a> {
    BoundVar(&'a mut BoundVariable, BoundVarIndex),
    FreeVar(&'a mut FreeVariable, FreeVarIndex),
    Abs(&'a mut Abstraction, AbsIndex),
    App(&'a mut Application, AppIndex),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FreeVariable {
    // The number of abstractions above the root that this Index node binds to
    // For example, in λ x, if x = 2, then we have a free bind of 1
    // If x = 3, then we have a free bind of 2, and so on.
    // Zero is not a valid value for this because we start 1-indexed
    // Note that this is NOT a debruijn index, it's a debruijn depth, as it always refers
    // to a constant number of abstractions above the root, no matter how deeply nested the
    // actual index is
    pub height: NonZeroU32,
}

impl Display for FreeVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "free ({})", self.height)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoundVariable {
    pub prev: BackingIndex,
    pub next: Option<BoundVarIndex>,
    pub parent: ParentEdge,
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
    pub fn prev(&self, tree: &FlatTree) -> PrevIndex {
        match tree.get_ref(self.prev) {
            NodeRef::BoundVar(_, bound_var) => PrevIndex::Var(bound_var),
            NodeRef::Abs(_, abs) => PrevIndex::Abs(abs),
            node_ref => panic!(
                "Expected bound variable or abstraction at {}, got free var: {:?}",
                self.prev,
                node_ref.clone_node()
            ),
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

#[derive(Debug, Clone, Copy)]
pub struct Application {
    pub func: BackingIndex,
    pub arg: BackingIndex,
}

/// #################
/// # BACKING INDEX #
/// #################

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

// Helper type -- the BackingIndex within this struct must point to a Node::FreeVar
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FreeVarIndex(pub BackingIndex);
impl Display for FreeVarIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

// Helper type -- the BackingIndex within this struct must point to a Node::BoundVar
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

// Helper type -- the BackingIndex within this struct must point to a Node::App
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AppIndex(pub BackingIndex);
impl Display for AppIndex {
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
pub enum ParentEdge {
    /// The "edge" has no parent, and the child here is the root of the tree
    IntoRoot,
    /// The edge is an abstraction to body edge, and the BackingIndex here is the index for the abstraction
    AbsToBody(AbsIndex),
    /// The edge is an application to function edge, and the BackingIndex here is the index for the application
    AppToFunc(AppIndex),
    /// The edge is an application to argument edge, and the BackingIndex here is the index for the application
    AppToArg(AppIndex),
}
impl ParentEdge {
    pub fn parent(&self) -> Option<BackingIndex> {
        match self {
            ParentEdge::IntoRoot => None,
            ParentEdge::AbsToBody(abs) => Some(abs.0),
            ParentEdge::AppToFunc(app) => Some(app.0),
            ParentEdge::AppToArg(app) => Some(app.0),
        }
    }
}

// #############
// # NORMALIZE #
// #############
pub fn normalize(tree: &FlatTree) -> FlatTree {
    let alive_count = tree.alive_count();
    let mut new_tree = FlatTree::with_capacity(alive_count);
    normalize_into(tree, &mut new_tree);
    new_tree
}

pub fn normalize_into(old_tree: &FlatTree, new_tree: &mut FlatTree) {
    struct Contour {
        old_abs: AbsIndex,
        new_abs: AbsIndex,
    }

    struct Context<'a> {
        old_tree: &'a FlatTree,
        new_tree: &'a mut FlatTree,
        contours: Vec<Contour>,
    }

    impl<'a> Context<'a> {
        fn push(&mut self, old_abs_index: AbsIndex, new_abs_index: AbsIndex) {
            let contour = Contour {
                old_abs: old_abs_index,
                new_abs: new_abs_index,
            };
            self.contours.push(contour);
        }

        fn pop(&mut self) {
            self.contours.pop();
        }

        fn old_to_new(&self, old_abs: AbsIndex) -> AbsIndex {
            self.contours
                .iter()
                .find_map(|contour| {
                    if contour.old_abs == old_abs {
                        Some(contour.new_abs)
                    } else {
                        None
                    }
                })
                .unwrap()
        }

        fn add_to_contour(&mut self, new_abs: AbsIndex, new_var_index: BoundVarIndex) {
            // Fixup abs entrance
            let abs = self.new_tree.get_abs_mut(new_abs);
            let entrance = abs.entrance;
            abs.entrance = Some(new_var_index);

            // Fixup bound var next + prev
            let new_var = self.new_tree.get_bound_var_mut(new_var_index);
            new_var.next = entrance;
            new_var.prev = new_abs.0;

            // Fixup the head-of-contour bound var, if one exists
            if let Some(entrance) = entrance {
                let entrance = self.new_tree.get_bound_var_mut(entrance);
                entrance.prev = new_var_index.0;
            }
        }
    }

    fn _normalize(
        ctx: &mut Context,
        old_node_index: BackingIndex,
        parent: ParentEdge,
    ) -> BackingIndex {
        match ctx.old_tree.get_ref(old_node_index) {
            NodeRef::FreeVar(free, _) => ctx.new_tree.alloc_free_var(*free),
            NodeRef::BoundVar(old_var, _) => {
                let old_abs_idx = ctx.old_tree.get_binding_abs(old_var);
                let new_abs = ctx.old_to_new(old_abs_idx);

                let new_var_index = ctx.new_tree.alloc_blank_var(parent);

                // Push newly allocated bound var into contour of abs
                ctx.add_to_contour(new_abs, new_var_index);

                new_var_index.0
            }
            NodeRef::Abs(old_abs, old_abs_index) => {
                let old_body_index = old_abs.body;

                let new_abs_index = ctx.new_tree.alloc_blank_abs();

                ctx.push(old_abs_index, new_abs_index);
                let new_body =
                    _normalize(ctx, old_body_index, ParentEdge::AbsToBody(new_abs_index));
                ctx.pop();

                let abs = ctx.new_tree.get_abs_mut(new_abs_index);
                abs.body = new_body;

                new_abs_index.0
            }
            NodeRef::App(application, _) => {
                let old_func_index = application.func;
                let old_arg_index = application.arg;
                let new_app_index = ctx.new_tree.alloc_blank_app();

                let new_func =
                    _normalize(ctx, old_func_index, ParentEdge::AppToFunc(new_app_index));
                let new_arg = _normalize(ctx, old_arg_index, ParentEdge::AppToArg(new_app_index));

                let new_app = ctx.new_tree.get_app_mut(new_app_index);
                new_app.func = new_func;
                new_app.arg = new_arg;
                new_app_index.0
            }
        }
    }

    let mut ctx = Context {
        old_tree,
        new_tree,
        contours: vec![],
    };

    let root_node = _normalize(&mut ctx, old_tree.root, ParentEdge::IntoRoot);
    new_tree.root = root_node;
}

pub fn check_contours(tree: &FlatTree) -> ContourResult<()> {
    struct Context<'a> {
        tree: &'a FlatTree,
        contours: HashMap<AbsIndex, Vec<BoundVarIndex>>,
        alive: HashSet<BackingIndex>,
    }

    impl<'a> Context<'a> {
        fn check_prev_index(&self, index: BackingIndex) -> ContourResult<PrevIndex> {
            self.check_not_garbage(index)?;
            match self.tree.get_ref(index) {
                NodeRef::BoundVar(_, index) => Ok(PrevIndex::Var(index)),
                NodeRef::Abs(_, index) => Ok(PrevIndex::Abs(index)),
                noderef => Err(ContourError::ExpectedAbsOrBoundVar {
                    index,
                    actual: noderef.clone_node(),
                }),
            }
        }

        fn check_abs_index(&self, index: AbsIndex) -> ContourResult<&'a Abstraction> {
            self.check_not_garbage(index.0)?;
            match self.tree.get(index.0) {
                Node::Abs(abstraction) => ContourResult::Ok(abstraction),
                node => ContourResult::Err(ContourError::ExpectedAbs {
                    index,
                    actual: node.clone(),
                }),
            }
        }

        fn check_app_index(&self, index: AppIndex) -> ContourResult<&'a Application> {
            self.check_not_garbage(index.0)?;
            match self.tree.get(index.0) {
                Node::App(application) => ContourResult::Ok(application),
                node => ContourResult::Err(ContourError::ExpectedApp {
                    index,
                    actual: node.clone(),
                }),
            }
        }

        fn check_bound_var_index(&self, index: BoundVarIndex) -> ContourResult<&'a BoundVariable> {
            self.check_not_garbage(index.0)?;
            match self.tree.get(index.0) {
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

        fn check_binding_abs(&self, bound_var: BoundVarIndex) -> ContourResult<()> {
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

        fn mark_not_garbage(&mut self, node: BackingIndex) -> ContourResult<()> {
            let is_new_value = self.alive.insert(node);
            if is_new_value {
                Ok(())
            } else {
                Err(ContourError::LoopDetectedInTree { node })
            }
        }

        fn check_not_garbage(&self, node: BackingIndex) -> ContourResult<()> {
            if self.alive.contains(&node) {
                Ok(())
            } else {
                Err(ContourError::NodeIsGarbage { node })
            }
        }

        fn check_back_edge(&self, bound_var_index: BoundVarIndex) -> ContourResult<()> {
            let bound_var = *self.check_bound_var_index(bound_var_index)?;
            let parent_edge = bound_var.parent;
            match parent_edge {
                ParentEdge::IntoRoot => {
                    return Err(ContourError::MissingParent {
                        bound_var,
                        bound_var_index,
                    });
                }
                ParentEdge::AbsToBody(abs_index) => {
                    let abs = self.check_abs_index(abs_index)?;
                    if abs.body != bound_var_index.0 {
                        return Err(ContourError::BoundVarParentMismatch {
                            bound_var,
                            parent_edge,
                            actual_parent: Node::Abs(abs.clone()),
                        });
                    }
                }
                ParentEdge::AppToFunc(app_index) => {
                    let app = self.check_app_index(app_index)?;
                    if app.func != bound_var_index.0 {
                        return Err(ContourError::BoundVarParentMismatch {
                            bound_var,
                            parent_edge,
                            actual_parent: Node::App(app.clone()),
                        });
                    }
                }
                ParentEdge::AppToArg(app_index) => {
                    let app = self.check_app_index(app_index)?;
                    if app.arg != bound_var_index.0 {
                        return Err(ContourError::BoundVarParentMismatch {
                            bound_var,
                            parent_edge,
                            actual_parent: Node::App(app.clone()),
                        });
                    }
                }
            }
            Ok(())
        }
    }

    fn get_alive_nodes(ctx: &mut Context, node: BackingIndex) -> ContourResult<()> {
        ctx.mark_not_garbage(node)?;
        match ctx.tree.get(node) {
            Node::FreeVar(_) => (),
            Node::BoundVar(_) => (),
            Node::Abs(abstraction) => get_alive_nodes(ctx, abstraction.body)?,
            Node::App(application) => {
                get_alive_nodes(ctx, application.func)?;
                get_alive_nodes(ctx, application.arg)?;
            }
        }
        Ok(())
    }

    fn _check_contours(ctx: &mut Context, node: BackingIndex) -> ContourResult<()> {
        match ctx.tree.get_ref(node) {
            NodeRef::FreeVar(_, _) => Ok(()),
            NodeRef::BoundVar(_, bound_var) => {
                ctx.check_binding_abs(bound_var)?;
                ctx.check_back_edge(bound_var)?;
                Ok(())
            }
            NodeRef::Abs(abstraction, abs_idx) => {
                ctx.check_contour(abstraction, abs_idx)?;
                _check_contours(ctx, abstraction.body)
            }
            NodeRef::App(application, _) => {
                _check_contours(ctx, application.func)?;
                _check_contours(ctx, application.arg)
            }
        }
    }

    let mut ctx = Context {
        tree,
        contours: HashMap::new(),
        alive: HashSet::new(),
    };
    get_alive_nodes(&mut ctx, tree.root)?;
    _check_contours(&mut ctx, tree.root)?;

    Ok(())
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
    NodeIsGarbage {
        node: BackingIndex,
    },
    LoopDetectedInTree {
        node: BackingIndex,
    },
    BoundVarParentMismatch {
        bound_var: BoundVariable,
        parent_edge: ParentEdge,
        actual_parent: Node,
    },
    MissingParent {
        bound_var: BoundVariable,
        bound_var_index: BoundVarIndex,
    },
    ExpectedApp {
        index: AppIndex,
        actual: Node,
    },
}

// ###########
// # FLATTEN #
// ###########
pub fn flatten(debruijn: &Debruijn) -> FlatTree {
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

        fn alloc_var_and_add_to_contour(
            &mut self,
            debruijn_index: usize,
            parent: ParentEdge,
        ) -> BackingIndex {
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
                    parent,
                };
                let this_var_index = self.tree.alloc_bound_var(this_var);

                self.tree.fixup_next(*prev, this_var_index);

                *prev = PrevIndex::Var(this_var_index);

                this_var_index.0
            }
        }
    }

    fn _flatten(ctx: &mut Context, term: &Debruijn, parent: ParentEdge) -> BackingIndex {
        match term {
            Debruijn::Index(debruijn_index) => {
                ctx.alloc_var_and_add_to_contour(*debruijn_index, parent)
            }
            Debruijn::Abstraction { body } => {
                // Pre-allocation is needed here so that we can have a spot for the abstraction
                // node to reside in. We will need this value to be allocated by the time we
                // go to compute the binding for any variable nodes that depend on it.
                let abs_index = ctx.tree.alloc_blank_abs();

                ctx.push(abs_index);
                let body = _flatten(ctx, body, ParentEdge::AbsToBody(abs_index));
                ctx.pop();

                let abs = ctx.tree.get_abs_mut(abs_index);
                abs.body = body;

                abs_index.0
            }
            Debruijn::Application { func, arg } => {
                let app_index = ctx.tree.alloc_blank_app();

                let func = _flatten(ctx, func, ParentEdge::AppToFunc(app_index));
                let arg = _flatten(ctx, arg, ParentEdge::AppToArg(app_index));

                let app = ctx.tree.get_app_mut(app_index);
                app.func = func;
                app.arg = arg;

                app_index.0
            }
        }
    }

    let mut tree = FlatTree::new();
    let mut ctx = Context {
        tree: &mut tree,
        abs_chain: vec![],
    };
    let root_index = _flatten(&mut ctx, debruijn, ParentEdge::IntoRoot);
    tree.root = root_index;
    tree
}

// #############
// # UNFLATTEN #
// #############
fn unflatten(tree: &FlatTree) -> Debruijn {
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
        match ctx.tree.get_ref(index) {
            NodeRef::FreeVar(free_var, _) => {
                let index = compute_debruijn_index_free(&ctx.chain, free_var);
                Debruijn::Index(index)
            }
            NodeRef::BoundVar(bound_var, _) => {
                let debruijn_index = ctx.compute_debruijn_index(bound_var);
                Debruijn::Index(debruijn_index)
            }
            NodeRef::Abs(abstraction, abs) => {
                ctx.push(abs);
                let body = _from(ctx, abstraction.body);
                ctx.pop();
                Debruijn::Abstraction {
                    body: Box::new(body),
                }
            }
            NodeRef::App(application, _) => {
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
        let flat = normalize(&FlatTree::from(&original));
        let roundtripped = Debruijn::from(&flat);

        assert_eq!(
            original, roundtripped,
            "Expected {original}, got {roundtripped}",
        );
    }
}
