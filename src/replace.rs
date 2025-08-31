use std::rc::Rc;

use crate::debruijn::Debruijn;

#[derive(Debug, Clone, Copy)]
pub struct VisitOrder {
    emit_outermost_first: bool,
    emit_left_first: bool,
}

type TreeWalker = dyn Iterator<Item = Rc<Debruijn>>;

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

    pub fn get_iter(&self, root: Rc<Debruijn>) -> Box<TreeWalker> {
        match (self.emit_left_first, self.emit_outermost_first) {
            (true, true) => Box::new(PreOrder::normal(root)),
            (false, true) => Box::new(PreOrder::reverse(root)),
            (true, false) => todo!(),
            (false, false) => todo!(),
        }
    }
}

struct PreOrder {
    node_stack: Vec<Rc<Debruijn>>,
    reverse: bool,
}

impl PreOrder {
    fn normal(root: Rc<Debruijn>) -> PreOrder {
        PreOrder {
            node_stack: vec![root],
            reverse: false,
        }
    }

    fn reverse(root: Rc<Debruijn>) -> PreOrder {
        PreOrder {
            node_stack: vec![root],
            reverse: true,
        }
    }
}
impl Iterator for PreOrder {
    type Item = Rc<Debruijn>;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.node_stack.pop() {
            match node.as_ref() {
                Debruijn::Index(_) => Some(node),
                Debruijn::Abstraction { body } => {
                    self.node_stack.push(body.clone());
                    Some(node)
                }
                Debruijn::Application { func, arg } => {
                    let left = func.clone();
                    let right = arg.clone();
                    if self.reverse {
                        self.node_stack.push(left);
                        self.node_stack.push(right);
                    } else {
                        self.node_stack.push(right);
                        self.node_stack.push(left);
                    }

                    Some(node)
                }
            }
        } else {
            None
        }
    }
}

pub fn replace2(
    root: &Rc<Debruijn>,
    replacee: &Rc<Debruijn>,
    replacement: &Rc<Debruijn>,
) -> Rc<Debruijn> {
    if Rc::ptr_eq(&root, &replacee) {
        replacement.clone()
    } else {
        match root.as_ref() {
            Debruijn::Index(_) => root.clone(),
            Debruijn::Application { func, arg } => {
                let func = replace2(func, replacee, replacement);
                let arg = replace2(arg, replacee, replacement);
                Rc::new(Debruijn::Application { func, arg })
            }
            Debruijn::Abstraction { body } => {
                let body = replace2(body, replacee, replacement);
                Rc::new(Debruijn::Abstraction { body })
            }
        }
    }
}

#[cfg(test)]

mod test {
    use std::{collections::HashMap, rc::Rc};

    use crate::{
        debruijn::Debruijn,
        replace::{PreOrder, TreeWalker, replace2},
    };

    fn idx(a: usize) -> Rc<Debruijn> {
        Rc::new(Debruijn::Index(a))
    }

    fn def(body: &Rc<Debruijn>) -> Rc<Debruijn> {
        Rc::new(Debruijn::Abstraction { body: body.clone() })
    }

    fn call(a: &Rc<Debruijn>, b: &Rc<Debruijn>) -> Rc<Debruijn> {
        Rc::new(Debruijn::Application {
            func: a.clone(),
            arg: b.clone(),
        })
    }

    type NodeToName = HashMap<Rc<Debruijn>, String>;
    type NameToNode = HashMap<String, Rc<Debruijn>>;

    struct TestData {
        node_to_name: NodeToName,
        name_to_node: NameToNode,
        root: Rc<Debruijn>,
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
            let a = idx(0);
            let c = idx(1);
            let e = idx(2);
            let h = idx(3);
            let i = def(&h);
            let g = def(&i);
            let d = call(&c, &e);
            let b = call(&a, &d);
            let f = call(&b, &g);

            let nodes = [
                ("a".into(), a.clone()),
                ("b".into(), b.clone()),
                ("c".into(), c.clone()),
                ("d".into(), d.clone()),
                ("e".into(), e.clone()),
                ("f".into(), f.clone()),
                ("g".into(), g.clone()),
                ("h".into(), h.clone()),
                ("i".into(), i.clone()),
            ];
            let name_to_node = HashMap::from(nodes.clone());

            let node_to_name = nodes.iter().cloned().map(|(a, b)| (b, a)).collect();

            TestData {
                node_to_name,
                name_to_node,
                root: f.clone(),
            }
        }

        fn into_string(&self, order: &[Rc<Debruijn>]) -> String {
            order
                .iter()
                .map(|node| self.node_to_name[node].clone())
                .intersperse(", ".into())
                .collect()
        }

        fn from_string(&self, order: &str) -> Vec<Rc<Debruijn>> {
            order
                .split(",")
                .map(|string| self.name_to_node[string.trim()].clone())
                .collect()
        }
    }

    fn assert_ordering(test_data: TestData, expected_pretty: &str, ordering: &mut TreeWalker) {
        let expected = test_data.from_string(&expected_pretty);

        let actual: Vec<_> = ordering.collect();
        let actual_pretty = test_data.into_string(&actual);

        assert_eq!(
            actual, expected,
            "expected {expected_pretty}, got {actual_pretty}"
        );
    }

    // #[test]
    // fn test_preorder_nlr_treepaths() {
    //     let test_data = TestData::new();
    //     let preorder = PreOrder::normal(test_data.root.clone());
    //     for (node, treepath) in preorder {
    //         println!("{} {:?}", node, treepath);
    //         if let Some(treepath) = treepath {
    //             match node.as_ref() {
    //                 Debruijn::Application { .. } => {
    //                     let expected_node = treepath.get(test_data.root.as_ref());
    //                     match expected_node {
    //                         Ok(expected_node) => assert_eq!(*expected_node, *node),
    //                         Err(err) => {
    //                             panic!("Couldn't get path for {}: {err}", test_data.root)
    //                         }
    //                     }
    //                 }
    //                 Debruijn::Index(_) => panic!("Expected {node} to be applicatino"),
    //                 Debruijn::Abstraction { .. } => panic!("Expected {node} to be applicatino"),
    //             }
    //         }
    //     }
    // }

    #[test]
    fn test_preorder_nlr() {
        let test_data = TestData::new();
        let expected = "f, b, a, d, c, e, g, i, h";
        let mut preorder = PreOrder::normal(test_data.root.clone());
        assert_ordering(test_data, expected, &mut preorder);
    }

    #[test]
    fn test_preorder_reverse_nrl() {
        let test_data = TestData::new();
        let expected = "f, g, i, h, b, d, e, c, a";
        let mut preorder = PreOrder::reverse(test_data.root.clone());
        assert_ordering(test_data, expected, &mut preorder);
    }

    #[test]
    fn test_replace2() {
        let replacee: Rc<Debruijn> = Rc::new("λ λ λ 5 2 3".parse().unwrap());
        let new_fragment: Debruijn = "λ λ 6 7 8".parse().unwrap();

        //   1 (λ <replacee>) 2
        // = 1 (λ λ λ λ 5 2 3) 2
        let starting = call(&(call(&idx(1), &def(&replacee))), &idx(2));

        let actual = replace2(&starting, &replacee, &Rc::new(new_fragment));
        let expected: Debruijn = "1 (λ λ λ 6 7 8) 2".parse().unwrap();
        assert_eq!(*actual, expected, "Expected {expected}, got {actual}");
    }
}
