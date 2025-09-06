use std::ops::ControlFlow;

use crate::debruijn::{Debruijn, Root};

#[derive(Debug, Clone, Copy)]
pub struct VisitOrder {
    pub(crate) reverse: bool,
}

impl VisitOrder {
    pub const LEFT_OUTERMOST: VisitOrder = VisitOrder { reverse: false };
    pub const RIGHT_OUTERMOST: VisitOrder = VisitOrder { reverse: true };

    pub fn preorder_walk_mut<T>(
        &self,
        root: &mut Root,
        mut action: impl FnMut(&mut Debruijn) -> ControlFlow<T>,
    ) -> Option<T> {
        fn _preorder_walk_mut<T>(
            term: &mut Debruijn,
            action: &mut impl FnMut(&mut Debruijn) -> ControlFlow<T>,
            reverse: bool,
        ) -> ControlFlow<T> {
            action(term)?;

            match term {
                Debruijn::Index(_) => (),
                Debruijn::Application { func, arg } => {
                    if reverse {
                        _preorder_walk_mut(arg, action, reverse)?;
                        _preorder_walk_mut(func, action, reverse)?;
                    } else {
                        _preorder_walk_mut(func, action, reverse)?;
                        _preorder_walk_mut(arg, action, reverse)?;
                    }
                }
                Debruijn::Abstraction { body } => _preorder_walk_mut(body, action, reverse)?,
            }
            ControlFlow::Continue(())
        }

        _preorder_walk_mut(&mut root.0, &mut action, self.reverse).break_value()
    }

    pub fn preorder_walk<'a, T>(
        &self,
        root: &'a Root,
        mut action: impl FnMut(&'a Debruijn) -> ControlFlow<T>,
    ) -> Option<T> {
        fn _preorder_walk<'a, T>(
            term: &'a Debruijn,
            action: &mut impl FnMut(&'a Debruijn) -> ControlFlow<T>,
            reverse: bool,
        ) -> ControlFlow<T> {
            action(term)?;

            match term {
                Debruijn::Index(_) => (),
                Debruijn::Application { func, arg } => {
                    if reverse {
                        _preorder_walk(arg, action, reverse)?;
                        _preorder_walk(func, action, reverse)?;
                    } else {
                        _preorder_walk(func, action, reverse)?;
                        _preorder_walk(arg, action, reverse)?;
                    }
                }
                Debruijn::Abstraction { body } => _preorder_walk(body, action, reverse)?,
            }
            ControlFlow::Continue(())
        }

        _preorder_walk(&root.0, &mut action, self.reverse).break_value()
    }
}

#[cfg(test)]

mod test {
    use std::{collections::HashMap, ops::ControlFlow};

    use crate::{
        debruijn::{Debruijn, Root},
        replace::VisitOrder,
    };

    fn idx(a: usize) -> Debruijn {
        Debruijn::Index(a)
    }

    fn def(body: Debruijn) -> Debruijn {
        Debruijn::Abstraction {
            body: Box::new(body.clone()),
        }
    }

    fn call(a: Debruijn, b: Debruijn) -> Debruijn {
        Debruijn::Application {
            func: Box::new(a.clone()),
            arg: Box::new(b.clone()),
        }
    }

    type NodeToName = HashMap<Debruijn, String>;
    type NameToNode = HashMap<String, Debruijn>;

    struct TestData {
        root: Root,
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
            let a = ("a".to_string(), idx(0));
            let c = ("c".to_string(), idx(1));
            let e = ("e".to_string(), idx(2));
            let h = ("h".to_string(), idx(3));
            let i = ("i".to_string(), def(h.1.clone()));
            let g = ("g".to_string(), def(i.1.clone()));
            let d = ("d".to_string(), call(c.1.clone(), e.1.clone()));
            let b = ("b".to_string(), call(a.1.clone(), d.1.clone()));
            let f = ("f".to_string(), call(b.1.clone(), g.1.clone()));

            let root = Root(f.1.clone());

            let nodes = [a, b, c, d, e, f, g, h, i];
            let name_to_node = HashMap::from(nodes.clone());

            let node_to_name = nodes.iter().cloned().map(|(a, b)| (b, a)).collect();

            TestData {
                node_to_name,
                name_to_node,
                root,
            }
        }

        fn into_string(&self, order: &[&Debruijn]) -> String {
            order
                .iter()
                .map(|node| self.node_to_name[node].clone())
                .intersperse(", ".into())
                .collect()
        }

        fn from_string(&self, order: &str) -> Vec<&Debruijn> {
            order
                .split(",")
                .map(|string| &self.name_to_node[string.trim()])
                .collect()
        }
    }

    fn assert_ordering(test_data: TestData, expected_pretty: &str, visit_order: VisitOrder) {
        let expected = test_data.from_string(&expected_pretty);

        let mut actual = vec![];
        visit_order.preorder_walk(&test_data.root, |term| {
            actual.push(term);
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
