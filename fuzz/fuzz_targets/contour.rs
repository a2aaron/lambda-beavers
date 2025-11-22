#![no_main]

use libfuzzer_sys::{Corpus, arbitrary::Arbitrary, fuzz_target};

use lambda_beavers::{debruijn::Debruijn, reduce::Reducer};

#[derive(Arbitrary)]
struct DebruijnWrapper(Debruijn);

impl std::fmt::Debug for DebruijnWrapper {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[track_caller]
fn assert_contour(reducer: &Reducer) {
    if let Err(error) = reducer.tree.check_contours() {
        panic!("Error for tree {}: {error:?}", reducer.tree);
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
    // println!("TEST CASE = {debruijn}");
    let mut reducer = Reducer::new(&debruijn.0);

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
    Corpus::Keep
});
