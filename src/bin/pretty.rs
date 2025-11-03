use std::str::FromStr;

use lambda_beavers::debruijn::Debruijn;

fn main() {
    let input = r"2(1)
\\
(\\1(20)2)(20)\2\\\22\\\

yyyyyy(22)y5\\y5\\
(\\1
(20)2)(20)\2\(1)


22";
    let term = Debruijn::from_str(input).unwrap();
    println!("{term}");
}
