use crate::debruijn::{Debruijn, Root};

#[derive(Debug, Clone, Copy)]
pub struct VisitOrder {
    emit_outermost_first: bool,
    emit_left_first: bool,
}

// i'm the original
pub trait TreeWalker<'a> = Iterator<Item = &'a Debruijn>;

impl VisitOrder {
    pub const LEFT_INNERMOST: VisitOrder = VisitOrder {
        emit_outermost_first: false,
        emit_left_first: true,
    };
    pub const RIGHT_INNERMOST: VisitOrder = VisitOrder {
        emit_outermost_first: false,
        emit_left_first: false,
    };
    pub const LEFT_OUTERMOST: VisitOrder = VisitOrder {
        emit_outermost_first: true,
        emit_left_first: true,
    };
    pub const RIGHT_OUTERMOST: VisitOrder = VisitOrder {
        emit_outermost_first: true,
        emit_left_first: false,
    };

    pub fn get_iter<'a>(&self, root: &'a Root) -> impl TreeWalker<'a> + use<'a> {
        match (self.emit_left_first, self.emit_outermost_first) {
            (true, true) => PreOrder::normal(root),
            (false, true) => PreOrder::reverse(root),
            (true, false) => todo!(),
            (false, false) => todo!(),
        }
    }
}

struct PreOrder<'a> {
    node_stack: Vec<&'a Debruijn>,
    reverse: bool,
}

impl<'a> PreOrder<'a> {
    fn normal(root: &'a Root) -> PreOrder<'a> {
        PreOrder {
            node_stack: vec![&root.0],
            reverse: false,
        }
    }

    fn reverse(root: &'a Root) -> PreOrder<'a> {
        PreOrder {
            node_stack: vec![&root.0],
            reverse: true,
        }
    }
}
impl<'a> Iterator for PreOrder<'a> {
    type Item = &'a Debruijn;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.node_stack.pop() {
            match node {
                Debruijn::Index(_) => Some(node),
                Debruijn::Abstraction { body } => {
                    self.node_stack.push(&body);
                    Some(node)
                }
                Debruijn::Application { func, arg } => {
                    if self.reverse {
                        self.node_stack.push(func);
                        self.node_stack.push(arg);
                    } else {
                        self.node_stack.push(arg);
                        self.node_stack.push(func);
                    }

                    Some(node)
                }
            }
        } else {
            None
        }
    }
}
pub fn replace<'a>(root: &'a Root, replacee: &'a Debruijn, replacement: &Debruijn) -> Root {
    Root(_replace(&root.0, replacee, replacement))
}
fn _replace<'a>(node: &'a Debruijn, replacee: &'a Debruijn, replacement: &Debruijn) -> Debruijn {
    if std::ptr::eq(node, replacee) {
        replacement.clone()
    } else {
        match node {
            Debruijn::Index(_) => node.clone(),
            Debruijn::Application { func, arg } => {
                let func = Box::new(_replace(func, replacee, replacement));
                let arg = Box::new(_replace(arg, replacee, replacement));
                Debruijn::Application { func, arg }
            }
            Debruijn::Abstraction { body } => {
                let body = Box::new(_replace(body, replacee, replacement));
                Debruijn::Abstraction { body }
            }
        }
    }
}

#[cfg(test)]

mod test {
    use std::collections::HashMap;

    use crate::{
        debruijn::{Debruijn, Root},
        replace::{TreeWalker, VisitOrder, replace},
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

        let actual: Vec<_> = visit_order.get_iter(&test_data.root).collect();
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

    #[test]
    fn test_replace2() {
        let replacee: Debruijn = "λ λ λ 5 2 3".parse().unwrap();
        let new_fragment: Debruijn = "λ λ 6 7 8".parse().unwrap();

        //   1 (λ <replacee>) 2
        // = 1 (λ λ λ λ 5 2 3) 2
        let starting = Root(call(call(idx(1), def(replacee.clone())), idx(2)));

        let replacee = find(&starting.0, &replacee).unwrap();

        let actual = replace(&starting, &replacee, &new_fragment);
        let expected = Root("1 (λ λ λ 6 7 8) 2".parse().unwrap());
        assert_eq!(actual, expected, "Expected {expected}, got {actual}");
    }

    fn find<'a>(root: &'a Debruijn, value: &Debruijn) -> Option<&'a Debruijn> {
        if root == value {
            Some(root)
        } else {
            match root {
                Debruijn::Index(_) => None,
                Debruijn::Application { func, arg } => {
                    find(func, value).or_else(|| find(arg, value))
                }
                Debruijn::Abstraction { body } => find(body, value),
            }
        }
    }
}
