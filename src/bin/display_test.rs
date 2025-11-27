use std::{sync::LazyLock, time::Duration};

use clap::Parser;
use lambda_beavers::{
    reduce::ReductionResult,
    term::Classic,
    utils::strong_reduction_test::{parse_line, reduce_with_timeout},
};

const TESTS: &str = include_str!("../../tests/tests.txt");
static TEST_COUNT: LazyLock<u64> =
    LazyLock::new(|| TESTS.split('\n').filter(|x| x.contains(": ")).count() as _);

#[derive(Debug, Parser)]
struct Args {
    #[arg(value_parser = clap::value_parser!(u64).range(0..*TEST_COUNT))]
    tests: Vec<u64>,
    #[arg(short, long)]
    all: bool,
    #[arg(short, long, action)]
    run: bool,
    #[arg(short, long, action)]
    print: bool,
    #[arg(short, long, default_value("5"))]
    timeout: Option<u64>,
}

fn main() {
    let args = Args::parse();

    let tests = if args.all {
        (0..(*TEST_COUNT - 1)).collect::<Vec<_>>()
    } else {
        args.tests.clone()
    };

    for i in tests {
        run(i as _, &args);
    }
}

fn run(n: usize, args: &Args) {
    let test = TESTS.split('\n').nth(n).unwrap();
    let (starting, reduced) = parse_line(test);
    if args.print {
        println!("{}", test);
        println!("Starting (Classic): {}", Classic::from(&starting));
        println!("Starting (Debruijn): {}", starting);
        println!("Reduced  (Classic): {}", Classic::from(&reduced));
        println!("Reduced (Debruijn): {}", reduced);
    }

    if args.run {
        let timeout = args.timeout.map(Duration::from_secs);
        let (result, duration) = reduce_with_timeout(&starting, timeout);
        let duration = duration.as_millis();

        let message = match result {
            Some(result) => match result {
                ReductionResult::NormalForm(result) => {
                    if reduced != result {
                        panic!("Failed! Expected: {}, Actual: {}", reduced, result);
                    } else {
                        format!("Normal Form,{}", result)
                    }
                }
                ReductionResult::Irreducible => {
                    panic!("Failed: Expected: {}, Actual: <irreducible>", reduced)
                }
                ReductionResult::MaxReductionsReached => format!("Max Reductions Reached"),
            },
            None => "Timed out".to_string(),
        };
        println!("{n},{duration},{message}");
    }
}
