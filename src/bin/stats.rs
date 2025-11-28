use std::{sync::LazyLock, time::Instant};

use clap::Parser;
use lambda_beavers::{
    reduce::{GarbageCollectionStrategy, Reducer},
    term::Classic,
    utils::strong_reduction_test::parse_line,
};

const TESTS: &str = include_str!("../../tests/tests.txt");
static TEST_COUNT: LazyLock<u64> =
    LazyLock::new(|| TESTS.split('\n').filter(|x| x.contains(": ")).count() as _);

#[derive(Debug, Parser)]
struct Args {
    #[arg(value_parser = clap::value_parser!(u64).range(0..*TEST_COUNT))]
    test: u64,
    #[arg(short, long)]
    all: bool,
    #[arg(short, long, action)]
    show_terms: bool,
    #[arg(short, long, default_value("1"), value_parser = clap::value_parser!(u64).range(1..))]
    period: u64,
    #[arg(short, long)]
    gc_ratio: Option<f32>,
    #[arg(short, long)]
    timeout: Option<u64>,
}

fn main() {
    let args = Args::parse();

    run(args.test as _, &args);
}

fn run(n: usize, args: &Args) {
    let test = TESTS.split('\n').nth(n).unwrap();
    let (starting, reduced) = parse_line(test);
    if args.show_terms {
        println!("{}", test);
        println!("Starting (Classic): {}", Classic::from(&starting));
        println!("Starting (Debruijn): {}", starting);
        println!("Reduced  (Classic): {}", Classic::from(&reduced));
        println!("Reduced (Debruijn): {}", reduced);
    }

    let mut reducer = Reducer::new(&starting);
    if let Some(gc_ratio) = args.gc_ratio {
        reducer.gc_strategy = Some(GarbageCollectionStrategy::with_ratio(gc_ratio));
    }

    let now = Instant::now();
    let mut steps = 0;
    println!("Elasped (ms),Step,Total Size,Alive Nodes,Garbage Nodes,Garbage Ratio,Total GCs");

    loop {
        let elapsed = now.elapsed();
        if steps % args.period == 0 {
            let total_size = reducer.tree.total_count();
            let garbage_nodes = reducer.tree.garbage_count;
            let alive_nodes = reducer.tree.alive_count();
            let garbage_ratio = garbage_nodes as f32 / alive_nodes as f32;
            let total_gcs = reducer.total_gc;
            let elapsed = elapsed.as_millis();
            println!(
                "{elapsed},{steps},{total_size},{alive_nodes},{garbage_nodes},{garbage_ratio},{total_gcs}",
            );
        }
        steps += 1;
        let result = reducer.reduce_one();

        if result.is_some() {
            break;
        }

        if let Some(timeout) = args.timeout
            && now.elapsed().as_secs() > timeout
        {
            break;
        }
    }
}
