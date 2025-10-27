#![no_main]

use libfuzzer_sys::fuzz_target;

use std::str::FromStr;

use lambda_beaver::{debruijn::Debruijn, reduce::Reducer};

#[track_caller]
fn assert_usage(reducer: &Reducer) {
    if let Err((failing_term, actual, expected)) = reducer.root.check_usage() {
        panic!(
            "Expected usage to be {expected} but got {actual} for node {failing_term} in {}",
            reducer.root
        );
    }
}

fuzz_target!(|data: &[u8]| {
    let Ok(string) = std::str::from_utf8(data) else {
        return;
    };
    let Ok(root) = Debruijn::from_str(string) else {
        return;
    };
    let mut reducer = Reducer::new(&root);

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
