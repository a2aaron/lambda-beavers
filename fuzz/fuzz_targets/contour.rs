#![no_main]

use libfuzzer_sys::{Corpus, arbitrary::Arbitrary, fuzz_target};

use lambda_beavers::{
    debruijn::Debruijn,
    flat_tree::check_contours,
    reduce::{GarbageCollectionStrategy, Reducer},
};

#[derive(Arbitrary)]
struct DebruijnWrapper(Debruijn);

impl std::fmt::Debug for DebruijnWrapper {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[track_caller]
fn assert_contour(reducer: &Reducer) {
    if let Err(error) = check_contours(&reducer.tree) {
        if reducer.gc_strategy.is_none() {
            panic!("[GC = N] Error for tree {}: {error:?}", reducer.tree);
        } else {
            panic!("[GC = Y] Error for tree {}: {error:?}", reducer.tree);
        }
    }
}

fn assert_test_case(debruijn: &Debruijn, gc_strategy: Option<GarbageCollectionStrategy>) {
    let mut reducer = Reducer::new(debruijn);
    reducer.gc_strategy = gc_strategy;
    for _ in 0..10 {
        assert_contour(&reducer);
        reducer.reduce_one();
    }
}

fn is_valid(debruijn: &Debruijn, max_depth: usize) -> bool {
    if max_depth == 0 {
        return false;
    }
    match debruijn {
        Debruijn::Index(idx) => *idx > 0 && *idx < 1000,
        Debruijn::Application { func, arg } => {
            is_valid(func, max_depth - 1) && is_valid(arg, max_depth - 1)
        }
        Debruijn::Abstraction { body } => is_valid(body, max_depth - 1),
    }
}

fuzz_target!(|debruijn: DebruijnWrapper| -> Corpus {
    if !is_valid(&debruijn.0, 10) {
        return Corpus::Reject;
    }
    assert_test_case(&debruijn.0, None);
    assert_test_case(
        &debruijn.0,
        Some(GarbageCollectionStrategy::with_ratio(0.0)),
    );

    Corpus::Keep
});
