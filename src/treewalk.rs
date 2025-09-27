use std::ops::ControlFlow;

use crate::debruijn_flat::{
    Abstraction, Application, DebruijnIndex, DebruijnNode, FlatRoot, ParentAbstractionChain,
    TermWithParent,
};

pub trait ActionMut<T> =
    FnMut(&mut FlatRoot, TermWithParent, &ParentAbstractionChain) -> ControlFlow<T>;
pub trait Action<T> = FnMut(&FlatRoot, TermWithParent, &ParentAbstractionChain) -> ControlFlow<T>;

impl FlatRoot {
    pub fn preorder_walk<T>(&self, mut action: impl Action<T>) -> Option<T> {
        self.preorder_walk_at(TermWithParent::root(self), &mut action)
    }

    pub fn preorder_walk_at<T>(
        &self,
        term: TermWithParent,
        mut action: impl Action<T>,
    ) -> Option<T> {
        preorder_walk(self, term, &mut ParentAbstractionChain::new(), &mut action).break_value()
    }

    pub fn preorder_walk_mut<T>(&mut self, mut action: impl ActionMut<T>) -> Option<T> {
        preorder_walk_mut(
            self,
            TermWithParent::root(self),
            &mut ParentAbstractionChain::new(),
            &mut action,
        )
        .break_value()
    }

    pub fn preorder_walk_at_mut<T>(
        &mut self,
        term: TermWithParent,
        mut action: impl ActionMut<T>,
    ) -> Option<T> {
        preorder_walk_mut(self, term, &mut ParentAbstractionChain::new(), &mut action).break_value()
    }

    pub fn postorder_walk<T>(&self, mut action: impl PostOrderAction<T>) -> T {
        postorder_walk(
            self,
            TermWithParent::root(self),
            &mut ParentAbstractionChain::new(),
            &mut action,
        )
    }

    pub fn postorder_walk_at_mut<T>(
        &mut self,
        term: TermWithParent,
        mut action: impl PostOrderActionMut<T>,
    ) -> T {
        postorder_walk_mut(self, term, &mut ParentAbstractionChain::new(), &mut action)
    }
}

pub trait PostOrderAction<T> =
    FnMut(&FlatRoot, TermWithParent, &ParentAbstractionChain, ChildResults<T>) -> T;
pub trait PostOrderActionMut<T> =
    FnMut(&mut FlatRoot, TermWithParent, &ParentAbstractionChain, ChildResults<T>) -> T;
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
    term: TermWithParent,
    parent_chain: &mut ParentAbstractionChain,
    action: &mut impl PostOrderAction<T>,
) -> T {
    match root[term] {
        DebruijnNode::Index(idx) => action(root, term, &parent_chain, ChildResults::Index(idx)),
        DebruijnNode::Abstraction(abs) => {
            let body = abs.body(term.term);
            parent_chain.push(term.term);
            let body_result = postorder_walk(root, body, parent_chain, action);
            parent_chain.pop();

            let child_results = ChildResults::Abstraction { abs, body_result };
            action(root, term, &parent_chain, child_results)
        }
        DebruijnNode::Application(app) => {
            let arg = app.arg(term.term);
            let func = app.func(term.term);

            let func_result = postorder_walk(root, func, parent_chain, action);
            let arg_result = postorder_walk(root, arg, parent_chain, action);
            let child_results = ChildResults::Application {
                app,
                func_result,
                arg_result,
            };
            action(root, term, &parent_chain, child_results)
        }
    }
}

pub fn postorder_walk_mut<T>(
    root: &mut FlatRoot,
    term: TermWithParent,
    parent_chain: &mut ParentAbstractionChain,
    action: &mut impl PostOrderActionMut<T>,
) -> T {
    match root[term] {
        DebruijnNode::Index(idx) => action(root, term, &parent_chain, ChildResults::Index(idx)),
        DebruijnNode::Abstraction(abs) => {
            let body = abs.body(term.term);
            parent_chain.push(term.term);
            let body_result = postorder_walk_mut(root, body, parent_chain, action);
            parent_chain.pop();

            let child_results = ChildResults::Abstraction { abs, body_result };
            action(root, term, &parent_chain, child_results)
        }
        DebruijnNode::Application(app) => {
            let arg = app.arg(term.term);
            let func = app.func(term.term);

            let func_result = postorder_walk_mut(root, func, parent_chain, action);
            let arg_result = postorder_walk_mut(root, arg, parent_chain, action);
            let child_results = ChildResults::Application {
                app,
                func_result,
                arg_result,
            };
            action(root, term, &parent_chain, child_results)
        }
    }
}

pub fn preorder_walk<T>(
    root: &FlatRoot,
    term: TermWithParent,
    parent_chain: &mut ParentAbstractionChain,
    action: &mut impl Action<T>,
) -> ControlFlow<T> {
    action(root, term, &parent_chain)?;

    let term = term.term;
    match root[term] {
        DebruijnNode::Index(_) => (),
        DebruijnNode::Abstraction(abs) => {
            let body = abs.body(term);
            parent_chain.push(term);
            preorder_walk(root, body, parent_chain, action)?;
            parent_chain.pop();
        }
        DebruijnNode::Application(app) => {
            let arg = app.arg(term);
            let func = app.func(term);

            preorder_walk(root, func, parent_chain, action)?;
            preorder_walk(root, arg, parent_chain, action)?;
        }
    }
    ControlFlow::Continue(())
}

pub fn preorder_walk_mut<T>(
    root: &mut FlatRoot,
    term: TermWithParent,
    parent_chain: &mut ParentAbstractionChain,
    action: &mut impl ActionMut<T>,
) -> ControlFlow<T> {
    action(root, term, &parent_chain)?;

    let term = term.term;
    match root[term] {
        DebruijnNode::Index(_) => (),
        DebruijnNode::Abstraction(abs) => {
            let body = abs.body(term);
            parent_chain.push(term);
            preorder_walk_mut(root, body, parent_chain, action)?;
            parent_chain.pop();
        }
        DebruijnNode::Application(app) => {
            let arg = app.arg(term);
            let func = app.func(term);

            preorder_walk_mut(root, func, parent_chain, action)?;
            preorder_walk_mut(root, arg, parent_chain, action)?;
        }
    }
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
        DebruijnNode::Index(a)
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
        test_data.root.preorder_walk(|_, term, _| {
            actual.push(term.term);
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
