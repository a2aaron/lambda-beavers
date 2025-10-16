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
    let child_results = match root[term] {
        DebruijnNode::Index(idx) => ChildResults::Index(idx),
        DebruijnNode::Abstraction(abs) => {
            let body = abs.body(term.term);

            ctx.term = body;
            ctx.chain.push(body.as_parent().unwrap());
            let body_result = postorder_walk(root, ctx, action);
            ctx.chain.pop(body.as_parent().unwrap());
            ctx.term = term;

            ChildResults::Abstraction { abs, body_result }
        }
        DebruijnNode::Application(app) => {
            let arg = app.arg(term.term);
            let func = app.func(term.term);

            ctx.term = func;
            ctx.chain.push(func.as_parent().unwrap());
            let func_result = postorder_walk(root, ctx, action);
            ctx.chain.pop(func.as_parent().unwrap());

            ctx.term = arg;
            ctx.chain.push(arg.as_parent().unwrap());
            let arg_result = postorder_walk(root, ctx, action);
            ctx.chain.pop(arg.as_parent().unwrap());
            ctx.term = term;

            ChildResults::Application {
                app,
                func_result,
                arg_result,
            }
        }
    };

    let result = action(root, ctx, child_results);
    result
}

pub fn postorder_walk_mut<T>(
    root: &mut FlatRoot,
    ctx: &mut ActionCtx,
    action: &mut impl PostOrderActionMut<T>,
) -> T {
    let term = ctx.term;

    let child_results = match root[term] {
        DebruijnNode::Index(idx) => ChildResults::Index(idx),
        DebruijnNode::Abstraction(abs) => {
            let body = abs.body(term.term);

            ctx.term = body;
            ctx.chain.push(body.as_parent().unwrap());
            let body_result = postorder_walk_mut(root, ctx, action);
            ctx.chain.pop(body.as_parent().unwrap());
            ctx.term = term;

            ChildResults::Abstraction { abs, body_result }
        }
        DebruijnNode::Application(app) => {
            let arg = app.arg(term.term);
            let func = app.func(term.term);

            ctx.term = func;
            ctx.chain.push(func.as_parent().unwrap());
            let func_result = postorder_walk_mut(root, ctx, action);
            ctx.chain.pop(func.as_parent().unwrap());

            ctx.term = arg;
            ctx.chain.push(arg.as_parent().unwrap());
            let arg_result = postorder_walk_mut(root, ctx, action);
            ctx.chain.pop(arg.as_parent().unwrap());
            ctx.term = term;

            ChildResults::Application {
                app,
                func_result,
                arg_result,
            }
        }
    };

    let result = action(root, &ctx, child_results);
    result
}

pub fn preorder_walk<T>(
    root: &FlatRoot,
    ctx: &mut ActionCtx,
    action: &mut impl Action<T>,
) -> ControlFlow<T> {
    let term = ctx.term;
    action(root, ctx)?;

    match root[term.term] {
        DebruijnNode::Index(_) => (),
        DebruijnNode::Abstraction(abs) => {
            let body = abs.body(term.term);

            ctx.term = body;
            ctx.chain.push(body.as_parent().unwrap());
            preorder_walk(root, ctx, action)?;
            ctx.chain.pop(body.as_parent().unwrap());
            ctx.term = term;
        }
        DebruijnNode::Application(app) => {
            let arg = app.arg(term.term);
            let func = app.func(term.term);

            ctx.term = func;
            ctx.chain.push(func.as_parent().unwrap());
            preorder_walk(root, ctx, action)?;
            ctx.chain.pop(func.as_parent().unwrap());

            ctx.term = arg;
            ctx.chain.push(arg.as_parent().unwrap());
            preorder_walk(root, ctx, action)?;
            ctx.chain.pop(arg.as_parent().unwrap());
            ctx.term = term;
        }
    }
    ControlFlow::Continue(())
}

pub fn preorder_walk_mut<T>(
    root: &mut FlatRoot,
    ctx: &mut ActionCtx,
    action: &mut impl ActionMut<T>,
) -> ControlFlow<T> {
    let term = ctx.term;
    action(root, ctx)?;

    match root[term] {
        DebruijnNode::Index(_) => (),
        DebruijnNode::Abstraction(abs) => {
            let body = abs.body(term.term);
            ctx.term = body;
            ctx.chain.push(body.as_parent().unwrap());
            preorder_walk_mut(root, ctx, action)?;
            ctx.chain.pop(body.as_parent().unwrap());
            ctx.term = term;
        }
        DebruijnNode::Application(app) => {
            let arg = app.arg(term.term);
            let func = app.func(term.term);

            ctx.term = func;
            ctx.chain.push(func.as_parent().unwrap());
            preorder_walk_mut(root, ctx, action)?;
            ctx.chain.pop(func.as_parent().unwrap());

            ctx.term = arg;
            ctx.chain.push(arg.as_parent().unwrap());
            preorder_walk_mut(root, ctx, action)?;
            ctx.chain.pop(arg.as_parent().unwrap());
            ctx.term = term;
        }
    }
    ControlFlow::Continue(())
}

#[cfg(test)]

mod test {
    use std::{collections::HashMap, ops::ControlFlow, str::FromStr};

    use crate::debruijn_flat::{BackingIndex, DebruijnEdge, DebruijnNode, FlatRoot};

    fn idx(a: usize) -> DebruijnNode {
        DebruijnNode::idx(a)
    }

    fn def(body: usize) -> DebruijnNode {
        DebruijnNode::abs(DebruijnEdge::new(body), 0)
    }

    fn call(func: usize, arg: usize) -> DebruijnNode {
        DebruijnNode::app(DebruijnEdge::new(func), DebruijnEdge::new(arg))
    }

    type NodeToName = HashMap<BackingIndex, String>;
    type NameToNode = HashMap<String, BackingIndex>;

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
                ("f", 0),
                ("b", 1),
                ("a", 2),
                ("d", 3),
                ("c", 4),
                ("e", 5),
                ("g", 6),
                ("i", 7),
                ("h", 8),
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

        fn into_string(&self, order: &[BackingIndex]) -> String {
            order
                .iter()
                .map(|node| self.node_to_name[node].clone())
                .intersperse(", ".into())
                .collect()
        }

        fn from_string(&self, order: &str) -> Vec<BackingIndex> {
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

    #[test]
    fn test_preorder_chain_depth_1() {
        let root = FlatRoot::from_str("λ λ 1").unwrap();

        let mut node_index = 0;
        let expected_depths = [0, 1, 2];

        root.preorder_walk(|_root, ctx| {
            let expected = expected_depths[node_index];
            let actual = ctx.chain.debruijn_depth();
            assert_eq!(actual, expected);
            node_index += 1;
            ControlFlow::Continue::<()>(())
        });
    }

    #[test]
    fn test_preorder_chain_2() {
        let test_data = TestData::new();

        let mut node_index = 0;
        //                                 F  B  A  D  C  E  G  I, H
        let expected_depths = [0, 0, 0, 0, 0, 0, 0, 1, 2];

        test_data.root.preorder_walk(|_root, ctx| {
            let expected = expected_depths[node_index];
            let actual = ctx.chain.debruijn_depth();
            assert_eq!(
                expected, actual,
                "expected depth of {expected} got {actual} at {node_index} ({:?})",
                ctx.term
            );
            node_index += 1;
            ControlFlow::Continue::<()>(())
        });
    }

    #[test]
    fn test_preorder_subwalk() {
        // A - λ
        //     |
        // B - λ
        //     |
        // C - 1
        let root = FlatRoot::from_str("λ λ 1").unwrap();
        let node_a = root.root;
        let node_b = {
            let DebruijnNode::Abstraction(abs) = root[node_a] else {
                unreachable!()
            };
            abs.body
        };
        let node_c = {
            let DebruijnNode::Abstraction(abs) = root[node_b] else {
                unreachable!()
            };
            abs.body
        };

        let expected_nodes = [
            vec![node_a, node_b, node_c],
            vec![node_b, node_c],
            vec![node_c],
        ];

        let mut outer_walk_index = 0;
        root.preorder_walk(|root, ctx| {
            let mut inner_walk_index = 0;
            root.preorder_walk_at(ctx, |_root, ctx| {
                let actual = ctx.term.term;
                let expected = expected_nodes[outer_walk_index][inner_walk_index].index;
                assert_eq!(expected, actual, "expected TermIndex {expected}, got {actual} at {outer_walk_index},{inner_walk_index}");

                inner_walk_index += 1;
            });
            outer_walk_index += 1;
            ControlFlow::Continue::<()>(())
        });
    }

    #[test]
    fn test_preorder_subwalk_depth() {
        // A - λ
        //     |
        // B - λ
        //     |
        // C - 1
        let root = FlatRoot::from_str("λ λ 1").unwrap();
        // outer walk: A, B, C
        let expected_depths = [
            vec![0, 1, 2], // A B C
            vec![1, 2],    //   B C
            vec![2],       //     C
        ];

        let mut outer_walk_index = 0;
        root.preorder_walk(|root, ctx| {
            let mut inner_walk_index = 0;
            root.preorder_walk_at(ctx, |_root, ctx| {
                let expected = expected_depths[outer_walk_index][inner_walk_index];
                let actual = ctx.chain.debruijn_depth();
                assert_eq!(
                    expected, actual,
                    "expected depth of {expected} got {actual} at {outer_walk_index},{inner_walk_index}\n(ctx.term: {:?}, ter: {:?})",
                    ctx.term, root[ctx.term.term ]
                );

                inner_walk_index += 1;
            });
            outer_walk_index += 1;
            ControlFlow::Continue::<()>(())
        });
    }

    #[test]
    fn test_preorder_immutability() {
        let root =
            FlatRoot::from_str("(λ λ λ 3 1 (2 1)) ((λ λ 2) (λ λ λ 3 1 (2 1))) λ λ 2").unwrap();

        root.preorder_walk(|root, ctx| {
            let old_chain = ctx.chain.clone();
            let old_term = ctx.term.clone();

            root.preorder_walk_at(ctx, |_root, _ctx| {});

            assert_eq!(old_chain, *ctx.chain);
            assert_eq!(old_term, ctx.term);
            ControlFlow::Continue::<()>(())
        });
    }
}
