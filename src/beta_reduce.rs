use crate::{
    flat_tree::{
        AbsIndex, BackingIndex, BoundVarIndex, DebruijnDepth, FlatTree, Node, NodeRef, ParentEdge,
    },
    graphviz,
};

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
        match ctx.tree.get_ref(node_index) {
            NodeRef::FreeVar(_, _) => (), // Free variable will never be substituted
            NodeRef::BoundVar(bound_var, _) => {
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
            NodeRef::Abs(abstraction, abs) => {
                _substitute(ctx, abstraction.body, ParentEdge::AbsToBody(abs))
            }
            NodeRef::App(application, _) => {
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
        match tree.get_ref(old_node_index) {
            NodeRef::FreeVar(free_var, _) => {
                let node = Node::FreeVar(*free_var);
                tree.alloc(node)
            }
            NodeRef::BoundVar(variable, _) => {
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
            NodeRef::Abs(abstraction, old_abs) => {
                let old_body_index = abstraction.body;

                let new_abs_index = tree.alloc_blank_abs();

                ctx.push(old_abs, new_abs_index);
                let new_body = _clone_subtree(tree, ctx, old_body_index);
                ctx.pop();

                let new_abs = tree.get_abs_mut(new_abs_index);
                new_abs.body = new_body;

                new_abs_index.0
            }
            NodeRef::App(application, _) => {
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
    if parent.parent() == Some(child) {
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
        if let Node::App(app) = tree.get(term) {
            if let Node::Abs(_) = tree.get(app.func) {
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    pub fn try_get(
        tree: &FlatTree,
        debruijn_depth: DebruijnDepth,
        parent_to_app: ParentEdge,
        app_index: BackingIndex,
    ) -> Option<RedexMut> {
        if let NodeRef::App(app, _) = tree.get_ref(app_index) {
            if let NodeRef::Abs(abs, func_index) = tree.get_ref(app.func) {
                let redex = RedexMut {
                    debruijn_depth,
                    parent_to_app,
                    app_index,
                    func_index,
                    body_index: abs.body,
                    arg_index: app.arg,
                };
                return Some(redex);
            }
        }
        None
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
            match ctx.tree.get_ref(index) {
                NodeRef::FreeVar(_, _) => (),
                NodeRef::BoundVar(_, _) => (),
                NodeRef::Abs(abstraction, index) => {
                    ctx.debruijn_depth += 1;
                    _get_redexes(ctx, abstraction.body, ParentEdge::AbsToBody(index));
                    ctx.debruijn_depth -= 1;
                }
                NodeRef::App(application, _) => {
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
            match tree.get_ref(index) {
                NodeRef::FreeVar(_, _) => false,
                NodeRef::BoundVar(_, _) => false,
                NodeRef::Abs(abstraction, _) => _is_bnf(tree, abstraction.body),
                NodeRef::App(application, _) => {
                    !RedexMut::is_redex(tree, index)
                        && _is_bnf(tree, application.func)
                        && _is_bnf(tree, application.arg)
                }
            }
        }

        _is_bnf(self, self.root)
    }
}
