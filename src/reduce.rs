use std::fmt::Display;

use clap::ValueEnum;

use crate::{
    beta_reduce::{self, RedexMut},
    debruijn::Debruijn,
    flat_tree::{BackingIndex, DebruijnDepth, FlatTree, NodeRef, ParentEdge, normalize_into},
    graphviz,
    utils::Rng,
};

pub enum WalkResult {
    StackIsEmpty,
    None,
    Some(RedexMut),
}

#[derive(Debug, Clone, Copy)]
pub struct WalkFrame {
    pub index: BackingIndex,
    pub parent: ParentEdge,
    pub depth: DebruijnDepth,
    pub state: WalkState,
}

impl WalkFrame {
    fn first_visit(index: BackingIndex, parent: ParentEdge, depth: DebruijnDepth) -> WalkFrame {
        WalkFrame {
            index,
            parent,
            depth,
            state: WalkState::FirstVisit,
        }
    }

    fn second_visit(frame: WalkFrame) -> WalkFrame {
        WalkFrame {
            state: WalkState::SecondVisit,
            ..frame
        }
    }

    fn third_visit(frame: WalkFrame) -> WalkFrame {
        WalkFrame {
            state: WalkState::ThirdVisit,
            ..frame
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WalkState {
    FirstVisit,
    SecondVisit,
    ThirdVisit,
}

// State required to walk the tree to find a redex
// We want to do left-outermost as our reduction strategy, but restarting a walk every time we
// finish up a beta reduction is very slow. Instead, we'd like to continue walking from around
// where we had found the redex.
// Consider how a tree looks before and after beta reduction:
// Before:
//   parent
//     |
//    app
//   /   \
// func  arg
//  |
// body
// After
//   parent
//     |
//    /
//   /
//  |
//  |
// new_body
// Prior to beta reduction, there are no redexes above the application. This is beacuse we are
// reducing w/ left outermost, so the current redex we are at is the first one we would have
// encountered via preorder walking

// After beta reduction, there is only one way for a redex to appear above new_body--if new_body
// is an abstraction and parent is an application, then parent is a redex! Otherwise, there is
// no redex above new_body and the next redex to reduce must appear somewhere within new_body
// This suggests the following strategy to reduce:
// 1. Do preorder walking until you find the first redex
// 2. Save the current walk context. Note that this will effectively only consist of applications.
// 3. Reduce the redex
// 4. Check if the parent is an application. If so, restart the walk at that parent (with the expectation that it's redex
//    will be immediately processed)
// 5. Otherwise, continue the walk at new_body

pub struct WalkContext {
    pub stack: Vec<WalkFrame>,
}

impl WalkContext {
    pub fn push(&mut self, node: WalkFrame) {
        self.stack.push(node);
    }

    pub fn peek(&self) -> Option<WalkFrame> {
        self.stack.last().cloned()
    }

    pub fn pop(&mut self) -> Option<WalkFrame> {
        self.stack.pop()
    }

    pub fn new(tree: &FlatTree) -> WalkContext {
        WalkContext {
            stack: vec![WalkFrame::first_visit(tree.root, ParentEdge::IntoRoot, 0)],
        }
    }

    pub fn walk_one(&mut self, tree: &FlatTree) -> WalkResult {
        graphviz::debug_write_to_file_with_ctx(tree, Some(self), "walk");
        if let Some(frame) = self.pop() {
            let WalkFrame {
                index,
                parent,
                depth,
                state,
            } = frame;
            match tree.get_ref(index) {
                NodeRef::BoundVar(_, _) => (),
                NodeRef::FreeVar(_, _) => (),
                NodeRef::Abs(abstraction, index) => {
                    self.push(WalkFrame::first_visit(
                        abstraction.body,
                        ParentEdge::AbsToBody(index),
                        depth + 1,
                    ));
                }
                NodeRef::App(application, app_index) => {
                    match state {
                        WalkState::FirstVisit => {
                            if let Some(redex) = RedexMut::try_get(tree, depth, parent, app_index) {
                                // Don't push anything onto the stack--we expect this redex to be processed before returning to walk_one
                                return WalkResult::Some(redex);
                            } else {
                                self.push(WalkFrame::second_visit(frame));

                                // Note that we want func to be visited before arg--it turns out that most of the
                                // time, redexes live in the function half rather than the argument half.
                                self.push(WalkFrame::first_visit(
                                    application.func,
                                    ParentEdge::AppToFunc(app_index),
                                    depth,
                                ));
                            }
                        }
                        WalkState::SecondVisit => {
                            self.push(WalkFrame::third_visit(frame));
                            self.push(WalkFrame::first_visit(
                                application.arg,
                                ParentEdge::AppToArg(app_index),
                                depth,
                            ));
                        }
                        WalkState::ThirdVisit => (),
                    }
                }
            }
            WalkResult::None
        } else {
            WalkResult::StackIsEmpty
        }
    }
}

pub struct GarbageCollectionStrategy {
    // Ratio of garbage nodes to alive nodes to determine when to do GC
    minimum_ratio: f32,
    other_tree: FlatTree,
}

impl GarbageCollectionStrategy {
    pub fn with_ratio(minimum_ratio: f32) -> GarbageCollectionStrategy {
        GarbageCollectionStrategy {
            minimum_ratio,
            other_tree: FlatTree::new(),
        }
    }
}

pub struct Reducer {
    pub tree: FlatTree,
    walk_ctx: WalkContext,
    pub gc_strategy: Option<GarbageCollectionStrategy>,
    pub total_gc: usize,
}

impl Reducer {
    pub fn new(term: &Debruijn) -> Self {
        let tree = FlatTree::from(term);
        Self {
            walk_ctx: WalkContext::new(&tree),
            tree,
            gc_strategy: None,
            total_gc: 0,
        }
    }

    fn find_redex(&mut self) -> Option<RedexMut> {
        loop {
            match self.walk_ctx.walk_one(&self.tree) {
                WalkResult::StackIsEmpty => break,
                WalkResult::None => continue,
                WalkResult::Some(redex_mut) => return Some(redex_mut),
            }
        }
        None
    }

    fn should_gc(&self) -> bool {
        if let Some(gc_strategy) = &self.gc_strategy {
            let garbage_count = self.tree.garbage_count;
            let alive_count = self.tree.alive_count();
            let garbage_ratio = garbage_count as f32 / alive_count as f32;
            garbage_ratio > gc_strategy.minimum_ratio
        } else {
            false
        }
    }

    fn perform_gc(&mut self) {
        if let Some(gc) = &mut self.gc_strategy {
            let alive_count = self.tree.alive_count();
            let other_capacity = gc.other_tree.backing.capacity();
            if alive_count > other_capacity {
                let additional = alive_count - other_capacity;
                gc.other_tree.backing.reserve(additional);
            }

            gc.other_tree.backing.clear();
            gc.other_tree.garbage_count = 0;
            normalize_into(&self.tree, &mut gc.other_tree);
            std::mem::swap(&mut self.tree, &mut gc.other_tree);

            // Need to reset the walk context to the beginning, as all of it's pointers are now stale
            self.walk_ctx = WalkContext::new(&self.tree);
            self.total_gc += 1;
        }
    }

    pub fn reduce_one(&mut self) -> Option<ReductionResult> {
        if let Some(redex) = self.find_redex() {
            let new_body = beta_reduce::beta_reduce(&mut self.tree, &redex);

            if self.should_gc() {
                self.perform_gc();
            } else {
                self.fixup_walkcontext_after_reduction(new_body, redex);
            }
            None
        } else {
            // This clone is fine, it occurs at the end of all reductions
            Some(ReductionResult::NormalForm(Debruijn::from(&self.tree)))
        }
    }

    fn fixup_walkcontext_after_reduction(&mut self, new_body: BackingIndex, redex: RedexMut) {
        // If the most recent application is the immediate parent of the redex, revisit it to check if it's a redex
        let should_rewalk_parent = if let Some(last_frame) = self.walk_ctx.stack.last_mut() {
            let is_app = matches!(self.tree.get_ref(last_frame.index), NodeRef::App(_, _));
            assert!(is_app);
            assert!(last_frame.state != WalkState::FirstVisit);

            if let Some(immediate_parent) = redex.parent_to_app.parent()
                && immediate_parent == last_frame.index
            {
                Some(last_frame)
            } else {
                None
            }
        } else {
            None
        };

        if let Some(last_frame) = should_rewalk_parent {
            // Re-walk the parent of the redex (because the parent is now a redex)
            last_frame.state = WalkState::FirstVisit;
        } else {
            // Walk the body instead
            let frame = WalkFrame::first_visit(new_body, redex.parent_to_app, redex.debruijn_depth);
            self.walk_ctx.push(frame)
        }
    }
}

pub enum ReductionResult {
    NormalForm(Debruijn),
    Irreducible,
    MaxReductionsReached,
}

impl Display for ReductionResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReductionResult::NormalForm(term) => write!(f, "Normal Form: {}", term),
            ReductionResult::Irreducible => write!(f, "Irreducible"),
            ReductionResult::MaxReductionsReached => write!(f, "Max Reductions Reached"),
        }
    }
}

pub fn reduce(term: &Debruijn, max_reductions: usize) -> (ReductionResult, usize) {
    let mut reducer = Reducer::new(term);
    for i in 0..max_reductions {
        if let Some(value) = reducer.reduce_one() {
            return (value, i);
        }
    }
    (ReductionResult::MaxReductionsReached, max_reductions)
}

pub enum ReductionStrategy {
    DFS,
    BFS,
    Random(Rng),
}

impl ReductionStrategy {
    pub fn random() -> ReductionStrategy {
        ReductionStrategy::Random(Rng::new())
    }
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum ReductionStrategyKind {
    DFS,
    BFS,
    Random,
}

impl From<ReductionStrategyKind> for ReductionStrategy {
    fn from(value: ReductionStrategyKind) -> Self {
        match value {
            ReductionStrategyKind::DFS => ReductionStrategy::DFS,
            ReductionStrategyKind::BFS => ReductionStrategy::BFS,
            ReductionStrategyKind::Random => ReductionStrategy::random(),
        }
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::{
        debruijn::Debruijn,
        flat_tree::check_contours,
        reduce::{GarbageCollectionStrategy, Reducer, ReductionResult},
    };

    #[track_caller]
    fn run_contour_testcase(testcase: &str) {
        let term = Debruijn::from_str(testcase).unwrap();
        let mut reducer = Reducer::new(&term);
        reducer.gc_strategy = Some(GarbageCollectionStrategy::with_ratio(0.0));

        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[track_caller]
    fn assert_contour(reducer: &Reducer) {
        if let Err(error) = check_contours(&reducer.tree) {
            panic!("Error for tree {}: {error:?}", reducer.tree);
        }
    }

    #[test]
    fn parent_usage_simplest() {
        let term = Debruijn::from_str("λ (λ 1 1) (1 1)").unwrap();
        let mut reducer = Reducer::new(&term);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn parent_usage_open_terms() {
        let term = Debruijn::from_str("λ (λ 1 1) 99").unwrap();
        let mut reducer = Reducer::new(&term);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn parent_usage() {
        let term =
            Debruijn::from_str("(λ λ λ 3 1 (2 1)) ((λ λ 2) (λ λ λ 3 1 (2 1))) λ λ 2").unwrap();
        let mut reducer = Reducer::new(&term);

        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn parent_usage_another() {
        let term = Debruijn::from_str("(λ λ 3 2) (λ λ 2)").unwrap();
        let mut reducer = Reducer::new(&term);

        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn parent_usage2() {
        let term = Debruijn::from_str("(λ λ 1) 10").unwrap();
        let mut reducer = Reducer::new(&term);

        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn usage3() {
        let term = Debruijn::from_str("λ λ λ λ (λ λ 6) 2 1").unwrap();
        let mut reducer = Reducer::new(&term);

        reducer.reduce_one();
        println!("{}", reducer.tree);
        reducer.reduce_one();
        println!("{}", reducer.tree);
        assert_contour(&reducer);
    }

    #[test]
    fn usage4() {
        let term = Debruijn::from_str("λ ((λ λ 1) 99) 1 99").unwrap();
        let mut reducer = Reducer::new(&term);

        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn usage4_simpler() {
        let term = Debruijn::from_str("λ ((λ λ 1) 99) 1").unwrap();
        let mut reducer = Reducer::new(&term);

        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn parent_usage_simpler() {
        let term = Debruijn::from_str("λ (λ λ λ 2) 100").unwrap();
        let mut reducer = Reducer::new(&term);

        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn from_fuzzer() {
        let term = "λ (λ 1 λ 1) λ λ 3";
        let term = Debruijn::from_str(term).unwrap();
        let mut reducer = Reducer::new(&term);

        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn from_fuzzer2() {
        let term = "(λ 1 λ 3) λ 1";
        let term = Debruijn::from_str(term).unwrap();
        let mut reducer = Reducer::new(&term);

        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn from_fuzzer3() {
        let term = "(λ λ 2 1) λ 1";
        let term = Debruijn::from_str(term).unwrap();
        let mut reducer = Reducer::new(&term);

        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn parent_usage_simple_2() {
        let term = Debruijn::from_str("λ (λ λ 1) 100").unwrap();
        let mut reducer = Reducer::new(&term);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn fuzzer4() {
        let term = Debruijn::from_str("2 1 λ λ (λ λ 1 20 2) 20 λ 2 λ λ λ 22 λ λ λ λ λ λ λ λ λ 22 λ 5 λ λ λ 5 λ λ (λ λ 1 20 2) 20 λ 2 λ 1 22").unwrap();
        let mut reducer = Reducer::new(&term);
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn fuzzer5() {
        let term = Debruijn::from_str(
            "λ λ λ (7 13) λ λ λ λ λ λ λ λ λ λ λ λ λ λ λ (λ λ λ λ λ λ λ λ λ λ λ λ λ 13 13) λ λ λ λ λ λ λ λ λ λ λ λ λ λ λ λ (λ λ λ λ λ λ λ λ λ λ λ λ λ λ λ 15 λ 15) 15 λ λ λ λ λ λ λ λ 255",
        ).unwrap();
        let mut reducer = Reducer::new(&term);

        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn fuzzer6() {
        let testcase = "(λ λ 1) 99 λ (λ λ 1 3) 99 99";
        let term = Debruijn::from_str(testcase).unwrap();
        let mut reducer = Reducer::new(&term);

        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn fuzzer7() {
        let testcase = "(λ 1 1) (λ 1) 11";
        let term = Debruijn::from_str(testcase).unwrap();
        let mut reducer = Reducer::new(&term);

        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    #[test]
    fn fuzzer8() {
        let testcase = "λ (λ λ 2 1) (λ λ 2)";
        let term = Debruijn::from_str(testcase).unwrap();
        let mut reducer = Reducer::new(&term);

        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
        reducer.reduce_one();
        assert_contour(&reducer);
    }

    fn reference_reduce(term: &Debruijn) -> Debruijn {
        let mut term = term.clone();
        let result = crate::reference::reduce(&mut term, 20);
        match result {
            crate::reference::ReduceResult::NormalForm => term,
            crate::reference::ReduceResult::NotNormalForm => {
                panic!("Couldn't get reference reduction")
            }
        }
    }

    fn assert_matches_reference(testcase: &str) {
        let term = Debruijn::from_str(testcase).unwrap();
        let expected = reference_reduce(&term);

        let (actual, _) = crate::reduce::reduce(&term, 100);
        match actual {
            ReductionResult::NormalForm(actual) => {
                assert_eq!(actual, expected, "expected {expected}, got {actual}")
            }
            ReductionResult::Irreducible => {
                panic!("Couldn't reduce after 100 steps! (is irreducible)")
            }
            ReductionResult::MaxReductionsReached => {
                panic!("Couldn't reduce after 100 steps!")
            }
        }
    }

    #[test]
    fn fuzzer9() {
        let testcase = "(λ (λ 255) λ 1) 10";
        assert_matches_reference(testcase);
    }

    #[test]
    fn fuzzer10() {
        // λ λ λ 1 ((λ 1) ((λ 2) (λ 2))) 3
        // λ λ λ 1 ((λ 2) (λ 2)) 3
        // λ λ λ 1 1 3
        let testcase = "λ λ λ 1 ((λ 1) ((λ 2) (λ 2))) 3";
        assert_matches_reference(testcase);
    }

    #[test]
    fn fuzzer11() {
        // λ (λ 257 (1 1)) λ λ (λ 3) 2
        // λ 256 (λ λ (λ 3) 2) (λ λ (λ 3) 2)
        // λ 256 λ (λ (λ λ (λ 3) 2)) (λ λ (λ 3) 2)
        // λ 256 λ λ λ (λ 3) 2
        // λ 256 λ λ λ 2
        let testcase = "λ (λ 257 (1 1)) λ λ (λ 3) 2";
        assert_matches_reference(testcase);
    }

    #[test]
    fn contour_fuzzer1() {
        run_contour_testcase("λ (λ 61) 1");
    }

    #[test]
    fn contour_fuzzer2() {
        run_contour_testcase("(λ 1) λ 1");
    }

    #[test]
    fn contour_fuzzer3() {
        run_contour_testcase("λ λ (λ 2 512) 2");
    }
}
