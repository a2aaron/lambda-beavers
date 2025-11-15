#![no_main]

use arbitrary::Arbitrary;
use lambda_beavers::{debruijn::Debruijn, reduce, reference::ReduceResult};
use libfuzzer_sys::{Corpus, fuzz_target};

#[derive(Arbitrary)]
struct DebruijnWrapper(Debruijn);

impl std::fmt::Debug for DebruijnWrapper {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
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

fn try_reference_reduce(term: &Debruijn) -> Option<Debruijn> {
    let mut term = term.clone();
    let result = lambda_beavers::reference::reduce(&mut term, 20);
    match result {
        ReduceResult::NormalForm => Some(term),
        ReduceResult::NotNormalForm => None,
    }
}

fuzz_target!(|debruijn: DebruijnWrapper| -> Corpus {
    if !is_valid(&debruijn.0, 10) {
        return Corpus::Reject;
    }

    let expected = try_reference_reduce(&debruijn.0);
    if expected.is_none() {
        return Corpus::Reject;
    }
    let expected = expected.unwrap();

    let (actual, _) = reduce::reduce(&debruijn.0, 100);
    match actual {
        reduce::ReductionResult::NormalForm(debruijn) => {
            assert_eq!(debruijn, expected, "Expected {expected}, got {debruijn}")
        }
        reduce::ReductionResult::Irreducible => {
            panic!("Couldn't reduce after 100 steps! (is irreducible)")
        }
        reduce::ReductionResult::MaxReductionsReached => panic!("Couldn't reduce after 100 steps!"),
    }
    Corpus::Keep
});
