#![cfg(test)]

use lambda_beaver::{
    debruijn::Debruijn,
    parse,
    reduce::{ReductionResult, ReductionStrategy, reduce},
    replace::VisitOrder,
    term::Term,
};

const TESTS: &str = include_str!("tests.txt");

fn parse_line(line: &str) -> (Debruijn, Debruijn) {
    let mut split = line.split(": ");
    let throwaway = split.next().unwrap();
    let useful_part = split.next().unwrap();

    let mut split = useful_part.split(" - ");
    let starting = split.next().unwrap();
    let expected = split.next().unwrap();
    let starting = parse::binary::from_str(starting).unwrap();
    let expected = parse::binary::from_str(expected).unwrap();
    (starting, expected)
}

#[test]
fn run_all() {
    let mut reduction_strategy = ReductionStrategy::DFS;
    let visit_order = VisitOrder::LEFT_OUTERMOST;
    let max_reductions = 10_00;
    for line in TESTS.split('\n') {
        let (starting, expected) = parse_line(line);
        let (reduction_result, _) = reduce(
            &starting,
            &mut reduction_strategy,
            visit_order,
            max_reductions,
        );

        match reduction_result {
            ReductionResult::NormalForm(actual) => {
                assert_eq!(expected, actual, "expected {expected}, got {actual}")
            }
            ReductionResult::Irreducible => panic!("Should be reducable to normal form for {line}"),
            ReductionResult::MaxReductionsReached => {
                let starting_classic = Term::from(&starting);
                let expected_classic = Term::from(&expected);
                panic!(
                    "Timed out for {line}\n(starting: {starting}, expected: {expected})\n(starting: {starting_classic}, expected: {expected_classic})"
                )
            }
        }
    }
}
