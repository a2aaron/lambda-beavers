#![no_main]

use libfuzzer_sys::fuzz_target;

use lambda_beavers::{debruijn::Debruijn, reduce::Reducer};

#[track_caller]
fn assert_usage(reducer: &Reducer) {
    if let Err((failing_term, actual, expected)) = reducer.root.check_usage() {
        panic!(
            "Expected usage to be {expected} but got {actual} for node {failing_term} in {}",
            reducer.root
        );
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

fuzz_target!(|debruijn: Debruijn| {
    if !is_valid(&debruijn, 10) {
        return;
    }
    // println!("{debruijn}");
    let mut reducer = Reducer::new(&debruijn);

    assert_usage(&reducer);
    reducer.reduce_one();
    assert_usage(&reducer);
    reducer.reduce_one();
    assert_usage(&reducer);
    reducer.reduce_one();
    assert_usage(&reducer);
    reducer.reduce_one();
    assert_usage(&reducer);
    reducer.reduce_one();
    assert_usage(&reducer);
    reducer.reduce_one();
    assert_usage(&reducer);
    reducer.reduce_one();
    assert_usage(&reducer);
});
