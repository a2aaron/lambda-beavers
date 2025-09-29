use std::ops::ControlFlow;

use crate::debruijn_flat::{
    Abstraction, Application, DebruijnIndex, DebruijnNode, FlatRoot, ParentChain, TermWithParent,
};

// Important! All of these walk methods must treat ParentChain as "opaquely immutable". Basically,
// the caller of these walk methods should not see any mutation done to an ActionCtx--it is as if
// it has passed in an &ActionCtx instead of &mut ActionCtx
// The reason why we give an &mut ActionCtx at all is because the walk methods are allowed to
// mutate the ActionCtx **during** the walk, but since the walk will always return to the node
// it stopped at, this is fine.
// (This is is also why all of the walk_at methods do not allow for early exit. Unlike the normal
// walk methods where the caller never needs to supply an ActionCtx and it does that on it's own,
// the subtree walkers do get an outside ActionCtx. Hence, it will need to always crawl the whole subtree.
// There may exist a future where this is not required but for now I am doing it this way since it
// turns out all of the subtree crawling algorithms actually never require an early exit.)
// In particlar, this means that the Action and ActionMut closures should NOT mutate the ActionCtx
// and should pretend that it is an &ActionCtx

pub struct ActionCtx<'chain> {
    pub term: TermWithParent,
    pub chain: &'chain mut ParentChain,
}

pub trait ActionMut<T> = FnMut(&mut FlatRoot, &mut ActionCtx) -> ControlFlow<T>;
pub trait Action<T> = FnMut(&FlatRoot, &mut ActionCtx) -> ControlFlow<T>;

impl FlatRoot {
    pub fn preorder_walk<T>(&self, mut action: impl Action<T>) -> Option<T> {
        let mut ctx = ActionCtx {
            term: TermWithParent::root(self),
            chain: &mut ParentChain::new(self),
        };
        preorder_walk(self, &mut ctx, &mut action).break_value()
    }

    pub fn preorder_walk_at(
        &self,
        ctx: &mut ActionCtx,
        mut action: impl FnMut(&FlatRoot, &mut ActionCtx),
    ) {
        let _ = preorder_walk(self, ctx, &mut |root, ctx| {
            action(root, ctx);
            ControlFlow::Continue::<()>(())
        });
    }

    pub fn preorder_walk_mut<T>(&mut self, mut action: impl ActionMut<T>) -> Option<T> {
        let mut ctx = ActionCtx {
            term: TermWithParent::root(self),
            chain: &mut ParentChain::new(self),
        };
        preorder_walk_mut(self, &mut ctx, &mut action).break_value()
    }

    pub fn preorder_walk_at_mut(
        &mut self,
        ctx: &mut ActionCtx,
        mut action: impl FnMut(&mut FlatRoot, &mut ActionCtx),
    ) {
        let _ = preorder_walk_mut(self, ctx, &mut |root, ctx| {
            action(root, ctx);
            ControlFlow::Continue::<()>(())
        });
    }

    pub fn postorder_walk<T>(&self, mut action: impl PostOrderAction<T>) -> T {
        let mut ctx = ActionCtx {
            term: TermWithParent::root(self),
            chain: &mut ParentChain::new(self),
        };
        postorder_walk(self, &mut ctx, &mut action)
    }

    pub fn postorder_walk_at_mut<T>(
        &mut self,
        ctx: &mut ActionCtx,
        mut action: impl PostOrderActionMut<T>,
    ) -> T {
        postorder_walk_mut(self, ctx, &mut action)
    }
}

pub trait PostOrderAction<T> = FnMut(&FlatRoot, &ActionCtx, ChildResults<T>) -> T;
pub trait PostOrderActionMut<T> = FnMut(&mut FlatRoot, &ActionCtx, ChildResults<T>) -> T;
pub enum ChildResults<T> {
    Index(DebruijnIndex),
    Abstraction {
        abs: Abstraction,
        body_result: T,
    },
    Application {
        app: Application,
        func_result: T,
        arg_result: T,
    },
}
pub fn postorder_walk<T>(
    root: &FlatRoot,
    ctx: &mut ActionCtx,
    action: &mut impl PostOrderAction<T>,
) -> T {
    let term = ctx.term;
    ctx.chain.push(root, term.parent);
    let child_results = match root[term] {
        DebruijnNode::Index(idx) => ChildResults::Index(idx),
        DebruijnNode::Abstraction(abs) => {
            let body = abs.body(term.term);

            ctx.term = body;
            let body_result = postorder_walk(root, ctx, action);
            ctx.term = term;

            ChildResults::Abstraction { abs, body_result }
        }
        DebruijnNode::Application(app) => {
            let arg = app.arg(term.term);
            let func = app.func(term.term);

            ctx.chain.push(root, term.parent);
            ctx.term = func;
            let func_result = postorder_walk(root, ctx, action);
            ctx.term = arg;
            let arg_result = postorder_walk(root, ctx, action);
            ctx.term = term;
            ctx.chain.pop(root, term.parent);

            ChildResults::Application {
                app,
                func_result,
                arg_result,
            }
        }
    };
    let result = action(root, ctx, child_results);
    ctx.chain.pop(root, term.parent);
    result
}

pub fn postorder_walk_mut<T>(
    root: &mut FlatRoot,
    ctx: &mut ActionCtx,
    action: &mut impl PostOrderActionMut<T>,
) -> T {
    let term = ctx.term;
    ctx.chain.push(root, term.parent);
    let child_results = match root[term] {
        DebruijnNode::Index(idx) => ChildResults::Index(idx),
        DebruijnNode::Abstraction(abs) => {
            let body = abs.body(term.term);

            ctx.term = body;
            let body_result = postorder_walk_mut(root, ctx, action);
            ctx.term = term;

            ChildResults::Abstraction { abs, body_result }
        }
        DebruijnNode::Application(app) => {
            let arg = app.arg(term.term);
            let func = app.func(term.term);

            ctx.chain.push(root, term.parent);
            ctx.term = func;
            let func_result = postorder_walk_mut(root, ctx, action);
            ctx.term = arg;
            let arg_result = postorder_walk_mut(root, ctx, action);
            ctx.term = term;
            ctx.chain.pop(root, term.parent);

            ChildResults::Application {
                app,
                func_result,
                arg_result,
            }
        }
    };
    let result = action(root, &ctx, child_results);
    ctx.chain.pop(root, term.parent);
    result
}

pub fn preorder_walk<T>(
    root: &FlatRoot,
    ctx: &mut ActionCtx,
    action: &mut impl Action<T>,
) -> ControlFlow<T> {
    let term = ctx.term;
    ctx.chain.push(root, term.parent);
    action(root, ctx)?;

    match root[term.term] {
        DebruijnNode::Index(_) => (),
        DebruijnNode::Abstraction(abs) => {
            let body = abs.body(term.term);

            ctx.term = body;
            preorder_walk(root, ctx, action)?;
            ctx.term = term;
        }
        DebruijnNode::Application(app) => {
            let arg = app.arg(term.term);
            let func = app.func(term.term);

            ctx.term = func;
            preorder_walk(root, ctx, action)?;
            ctx.term = arg;
            preorder_walk(root, ctx, action)?;
            ctx.term = term;
        }
    }
    ctx.chain.pop(root, term.parent);
    ControlFlow::Continue(())
}

pub fn preorder_walk_mut<T>(
    root: &mut FlatRoot,
    ctx: &mut ActionCtx,
    action: &mut impl ActionMut<T>,
) -> ControlFlow<T> {
    let term = ctx.term;
    ctx.chain.push(root, term.parent);
    action(root, ctx)?;

    match root[term] {
        DebruijnNode::Index(_) => (),
        DebruijnNode::Abstraction(abs) => {
            let body = abs.body(term.term);
            ctx.term = body;
            preorder_walk_mut(root, ctx, action)?;
            ctx.term = term;
        }
        DebruijnNode::Application(app) => {
            let arg = app.arg(term.term);
            let func = app.func(term.term);

            ctx.term = func;
            preorder_walk_mut(root, ctx, action)?;
            ctx.term = arg;
            preorder_walk_mut(root, ctx, action)?;
            ctx.term = term;
        }
    }
    ctx.chain.pop(root, term.parent);
    ControlFlow::Continue(())
}

#[cfg(test)]

mod test {
    use std::{collections::HashMap, ops::ControlFlow};

    use crate::debruijn_flat::{DebruijnNode, FlatRoot, TermIndex};

    fn term_idx(i: usize) -> TermIndex {
        TermIndex::new(i)
    }

    fn idx(a: usize) -> DebruijnNode {
        DebruijnNode::idx(a)
    }

    fn def(body: usize) -> DebruijnNode {
        DebruijnNode::abs(TermIndex::new(body), 0)
    }

    fn call(func: usize, arg: usize) -> DebruijnNode {
        DebruijnNode::app(TermIndex::new(func), TermIndex::new(arg))
    }

    type NodeToName = HashMap<TermIndex, String>;
    type NameToNode = HashMap<String, TermIndex>;

    struct TestData {
        root: FlatRoot,
        node_to_name: NodeToName,
        name_to_node: NameToNode,
    }

    impl TestData {
        //      F
        //     / \
        //   B    G
        //  / \    \
        // A   D    I
        //    / \    \
        //   C   E    H
        fn new() -> TestData {
            let root = FlatRoot::from(vec![
                call(1, 6), // 0 | F -> B, G
                call(2, 3), // 1 | B -> A, D
                idx(0),     // 2 | A
                call(4, 5), // 3 | D -> C, E
                idx(1),     // 4 | C
                idx(2),     // 5 | E
                def(7),     // 6 | G -> I
                def(8),     // 7 | I -> H
                idx(3),     // 8 | H
            ]);

            let nodes = [
                ("f", term_idx(0)),
                ("b", term_idx(1)),
                ("a", term_idx(2)),
                ("d", term_idx(3)),
                ("c", term_idx(4)),
                ("e", term_idx(5)),
                ("g", term_idx(6)),
                ("i", term_idx(7)),
                ("h", term_idx(8)),
            ];

            let name_to_node = nodes
                .iter()
                .cloned()
                .map(|(a, b)| (a.to_string(), b))
                .collect();
            let node_to_name = nodes
                .iter()
                .cloned()
                .map(|(a, b)| (b, a.to_string()))
                .collect();

            TestData {
                node_to_name,
                name_to_node,
                root,
            }
        }

        fn into_string(&self, order: &[TermIndex]) -> String {
            order
                .iter()
                .map(|node| self.node_to_name[node].clone())
                .intersperse(", ".into())
                .collect()
        }

        fn from_string(&self, order: &str) -> Vec<TermIndex> {
            order
                .split(",")
                .map(|string| self.name_to_node[string.trim()])
                .collect()
        }
    }

    fn assert_ordering(test_data: TestData, expected_pretty: &str) {
        let expected = test_data.from_string(&expected_pretty);

        let mut actual = vec![];
        test_data.root.preorder_walk(|_root, ctx| {
            actual.push(ctx.term.term);
            ControlFlow::Continue::<()>(())
        });
        let actual_pretty = test_data.into_string(&actual);

        assert_eq!(
            actual, expected,
            "expected {expected_pretty}, got {actual_pretty}"
        );
    }

    #[test]
    fn test_preorder_nlr() {
        let test_data = TestData::new();
        let expected = "f, b, a, d, c, e, g, i, h";
        assert_ordering(test_data, expected);
    }
}
