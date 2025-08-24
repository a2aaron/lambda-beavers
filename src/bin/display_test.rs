use clap::Parser;
use lambda_beaver::{debruijn::Debruijn, parse, term::Term};

const TESTS: &str = include_str!("../../tests/tests.txt");

#[derive(Debug, Parser)]
struct Args {
    num: usize,
}

fn parse_line(line: &str) -> (Debruijn, Debruijn) {
    let mut split = line.split(": ");
    let _throwaway = split.next().unwrap();
    let useful_part = split.next().unwrap();

    let mut split = useful_part.split(" - ");
    let starting = split.next().unwrap();
    let expected = split.next().unwrap();
    let starting = parse::binary::from_str(starting).unwrap();
    let expected = parse::binary::from_str(expected).unwrap();
    (starting, expected)
}

fn main() {
    let args = Args::parse();
    let test = TESTS.split('\n').nth(args.num).unwrap();
    let (starting, reduced) = parse_line(test);
    println!("{}", test);
    println!("Starting (Classic): {}", Term::from(&starting));
    println!("Starting (Debruijn): {}", starting);
    println!("Reduced  (Classic): {}", Term::from(&reduced));
    println!("Reduced (Debruijn): {}", reduced);
}
