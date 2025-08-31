use std::time::Duration;

use clap::Parser;
use lambda_beaver::{
    replace::VisitOrder,
    term::Term,
    utils::strong_reduction_test::{parse_line, reduce_with_timeout},
};

const TESTS: &str = include_str!("../../tests/tests.txt");

#[derive(Debug, Parser)]
struct Args {
    start: usize,
    end: Option<usize>,
    #[arg(short, long, action)]
    run: bool,
    #[arg(short, long, action)]
    print: bool,
    #[arg(short, long, default_value("5"))]
    timeout: Option<u64>,
}

fn main() {
    let args = Args::parse();

    let n = args.start;

    if let Some(end) = args.end {
        for i in n..=end {
            run(i, &args);
        }
    } else {
        run(n, &args);
    }
}

fn run(n: usize, args: &Args) {
    let test = TESTS.split('\n').nth(n).unwrap();
    let (starting, reduced) = parse_line(test);
    if args.print {
        println!("{}", test);
        println!("Starting (Classic): {}", Term::from(&starting));
        println!("Starting (Debruijn): {}", starting);
        println!("Reduced  (Classic): {}", Term::from(&reduced));
        println!("Reduced (Debruijn): {}", reduced);
    }

    if args.run {
        let visit_order = VisitOrder::LEFT_OUTERMOST;
        let timeout = args.timeout.map(Duration::from_secs);
        let (result, duration) = reduce_with_timeout(&starting, visit_order, timeout);
        let duration = duration.as_millis();
        match result {
            Some(result) => println!("{n},{duration},{result}"),
            None => println!("{n},{duration},Timed out"),
        }
    }
}
