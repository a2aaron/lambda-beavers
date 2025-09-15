use std::ops::ControlFlow;

use crate::debruijn_flat::{DebruijnNode, FlatRoot, ParentChain, TermWithParent};

#[derive(Debug, Clone, Copy)]
pub struct VisitOrder {
    pub(crate) reverse: bool,
}

impl VisitOrder {
    pub const LEFT_OUTERMOST: VisitOrder = VisitOrder { reverse: false };
    pub const RIGHT_OUTERMOST: VisitOrder = VisitOrder { reverse: true };

    pub fn preorder_walk<T>(
        &self,
        root: &FlatRoot,
        mut action: impl FnMut(&FlatRoot, TermWithParent, &ParentChain) -> ControlFlow<T>,
    ) -> Option<T> {
        fn _preorder_walk<T>(
            root: &FlatRoot,
            term: TermWithParent,
            parent_chain: &mut ParentChain,
            action: &mut impl FnMut(&FlatRoot, TermWithParent, &ParentChain) -> ControlFlow<T>,
            reverse: bool,
        ) -> ControlFlow<T> {
            action(root, term, &parent_chain)?;

            let term = term.term;
            match root[term] {
                DebruijnNode::Index(_) => (),
                DebruijnNode::Abstraction { body, .. } => {
                    let body = TermWithParent::body(term, body);
                    parent_chain.push(term);
                    _preorder_walk(root, body, parent_chain, action, reverse)?;
                    parent_chain.pop();
                }
                DebruijnNode::Application { func, arg } => {
                    let arg = TermWithParent::arg(term, arg);
                    let func = TermWithParent::func(term, func);
                    if reverse {
                        _preorder_walk(root, arg, parent_chain, action, reverse)?;
                        _preorder_walk(root, func, parent_chain, action, reverse)?;
                    } else {
                        _preorder_walk(root, func, parent_chain, action, reverse)?;
                        _preorder_walk(root, arg, parent_chain, action, reverse)?;
                    }
                }
            }
            ControlFlow::Continue(())
        }

        let mut parent_chain = vec![];
        _preorder_walk(
            root,
            TermWithParent::root(root),
            &mut parent_chain,
            &mut action,
            self.reverse,
        )
        .break_value()
    }

    pub fn preorder_walk_mut<T>(
        &self,
        root: &mut FlatRoot,
        mut action: impl FnMut(&mut FlatRoot, TermWithParent, &ParentChain) -> ControlFlow<T>,
    ) -> Option<T> {
        fn _preorder_walk_mut<T>(
            root: &mut FlatRoot,
            term: TermWithParent,
            parent_chain: &mut ParentChain,
            action: &mut impl FnMut(&mut FlatRoot, TermWithParent, &ParentChain) -> ControlFlow<T>,
            reverse: bool,
        ) -> ControlFlow<T> {
            action(root, term, &parent_chain)?;

            let term = term.term;
            match root[term] {
                DebruijnNode::Index(_) => (),
                DebruijnNode::Abstraction { body, .. } => {
                    let body = TermWithParent::body(term, body);
                    parent_chain.push(term);
                    _preorder_walk_mut(root, body, parent_chain, action, reverse)?;
                    parent_chain.pop();
                }
                DebruijnNode::Application { func, arg } => {
                    let arg = TermWithParent::arg(term, arg);
                    let func = TermWithParent::func(term, func);
                    if reverse {
                        _preorder_walk_mut(root, arg, parent_chain, action, reverse)?;
                        _preorder_walk_mut(root, func, parent_chain, action, reverse)?;
                    } else {
                        _preorder_walk_mut(root, func, parent_chain, action, reverse)?;
                        _preorder_walk_mut(root, arg, parent_chain, action, reverse)?;
                    }
                }
            }
            ControlFlow::Continue(())
        }

        let mut parent_chain = vec![];
        _preorder_walk_mut(
            root,
            TermWithParent::root(root),
            &mut parent_chain,
            &mut action,
            self.reverse,
        )
        .break_value()
    }
}

#[cfg(test)]

mod test {
    use std::{collections::HashMap, ops::ControlFlow};

    use crate::{
        debruijn_flat::{DebruijnNode, FlatRoot, TermIndex},
        treewalk::VisitOrder,
    };

    fn idx(a: usize) -> DebruijnNode {
        DebruijnNode::Index(a)
    }

    fn def(body: usize) -> DebruijnNode {
        DebruijnNode::Abstraction {
            body: TermIndex(body),
            usage: 0,
        }
    }

    fn call(func: usize, arg: usize) -> DebruijnNode {
        DebruijnNode::Application {
            func: TermIndex(func),
            arg: TermIndex(arg),
        }
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
                ("f", TermIndex(0)),
                ("b", TermIndex(1)),
                ("a", TermIndex(2)),
                ("d", TermIndex(3)),
                ("c", TermIndex(4)),
                ("e", TermIndex(5)),
                ("g", TermIndex(6)),
                ("i", TermIndex(7)),
                ("h", TermIndex(8)),
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

    fn assert_ordering(test_data: TestData, expected_pretty: &str, visit_order: VisitOrder) {
        let expected = test_data.from_string(&expected_pretty);

        let mut actual = vec![];
        visit_order.preorder_walk(&test_data.root, |_, term, _| {
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
        assert_ordering(test_data, expected, VisitOrder::LEFT_OUTERMOST);
    }

    #[test]
    fn test_preorder_reverse_nrl() {
        let test_data = TestData::new();
        let expected = "f, g, i, h, b, d, e, c, a";
        assert_ordering(test_data, expected, VisitOrder::RIGHT_OUTERMOST);
    }
}
