use clap::Parser;
use std::collections::HashMap;

use lambda_beaver::{
    parse,
    reduce::{self, ReductionResult},
    replace::VisitOrder,
    term::Term,
    utils::{self},
};

struct Histogram(HashMap<String, usize>);
impl Histogram {
    fn new() -> Histogram {
        Histogram(HashMap::new())
    }

    fn add_irreducable(&mut self) {
        *self.0.entry("IR".to_string()).or_insert(0) += 1;
    }

    fn add_timeout(&mut self) {
        *self.0.entry("TO".to_string()).or_insert(0) += 1;
    }

    fn add(&mut self, value: usize) {
        *self.0.entry(format!("{value:02}")).or_insert(0) += 1;
    }

    fn print(&self) {
        let mut keys: Vec<String> = self.0.keys().cloned().collect();
        keys.sort();
        for key in keys {
            let value = self.0[&key];
            println!("{key}: {value}");
        }
    }
}

#[derive(Parser, Debug)]
#[command(about, long_about = None)]
struct Args {
    /// Minimum bitlength
    #[arg(long, default_value_t = 0)]
    min_bitlength: usize,
    /// Maximum bitlength
    #[arg(long, default_value_t = 25)]
    max_bitlength: usize,
    /// Maximum number of reductions
    #[arg(long, default_value_t = 1_000)]
    max_reductions: usize,
}

#[allow(unused_variables)]
fn main() {
    let args = Args::parse();
    let min_bitlength = args.min_bitlength;
    let max_bitlength = args.max_bitlength;
    let max_reductions = args.max_reductions;
    let visit_order = VisitOrder::LEFT_OUTERMOST;

    let mut histogram_lengths = Histogram::new();
    let mut histogram_time = Histogram::new();

    for length in min_bitlength..=max_bitlength {
        let terms = utils::bitstring_permutations(length)
            .filter_map(|bitstring| parse::binary::from_vec(bitstring).ok());

        for term in terms {
            let term_binary = format!("{term:b}");
            let term_classic = Term::from(&term);
            let (result, reductions_used) = reduce::reduce(&term, visit_order, max_reductions);
            match result {
                ReductionResult::NormalForm(bnf) => {
                    let bnf_classic = Term::from(&bnf);
                    let bnf_binary = format!("{:b}", bnf);
                    println!(
                        "{term_binary} -> {bnf_binary} | {term} -> {bnf} | {term_classic} -> {bnf_classic} | lengths: {} -> {} | found in {reductions_used}",
                        term_binary.len(),
                        bnf_binary.len(),
                    );
                    histogram_lengths.add(bnf_binary.len());
                    histogram_time.add(reductions_used);
                }
                ReductionResult::Irreducible => {
                    println!(
                        "{term_binary} | {term} | {term_classic} | <proved irreducible after {reductions_used} reductions>"
                    );
                    histogram_lengths.add_irreducable();
                    histogram_time.add_irreducable();
                }
                ReductionResult::MaxReductionsReached => {
                    println!(
                        "{term_binary} | {term} | {term_classic} | <not found after {reductions_used} reductions>"
                    );
                    histogram_lengths.add_timeout();
                    histogram_time.add_timeout();
                }
            }
        }
    }
    println!("Histogram - Lengths");
    histogram_lengths.print();
    println!("Histogram - Time");
    histogram_time.print();
}
