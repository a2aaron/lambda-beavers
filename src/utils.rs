/// Xorshift128+ implementation stolen from tiny-rng
/// https://docs.rs/tiny-rng/
#[derive(Clone, Copy)]
pub struct Rng {
    state: (u64, u64),
}

impl Rng {
    pub fn new() -> Self {
        let system_time = std::time::SystemTime::now();
        let seed = system_time
            .duration_since(std::time::UNIX_EPOCH)
            .expect("Time went backwards")
            .as_nanos() as u64;
        Rng::from_seed(seed)
    }

    pub fn from_seed(seed: u64) -> Self {
        Self {
            state: (
                seed ^ 0xf4dbdf2183dcefb7, // [crc32(b"0"), crc32(b"1")]
                seed ^ 0x1ad5be0d6dd28e9b, // [crc32(b"2"), crc32(b"3")]
            ),
        }
    }

    fn rand_u64(&mut self) -> u64 {
        let (mut x, y) = self.state;
        self.state.0 = y;
        x ^= x << 23;
        self.state.1 = x ^ y ^ (x >> 17) ^ (y >> 26);
        self.state.1.wrapping_add(y)
    }

    pub fn rand_usize(&mut self) -> usize {
        self.rand_u64() as usize
    }
}

pub fn bitstring_permutations(n: usize) -> impl Iterator<Item = Vec<bool>> {
    let two_pow_n = 1 << n;
    (0..two_pow_n).map(move |value| {
        // note: we want the first bool in the array to represent the high order bit
        // so we must iterate the bits in reverse order
        (0..n)
            .rev()
            .map(|bit_to_extract| {
                let extracted_bit = value >> bit_to_extract;
                let bottom_bit_is_one = (extracted_bit & 1) != 0;
                bottom_bit_is_one
            })
            .collect()
    })
}

pub mod strong_reduction_test {
    use std::time::{Duration, Instant};

    use crate::{
        debruijn::Root,
        parse,
        reduce::{Reducer, ReductionResult},
        replace::VisitOrder,
    };

    pub fn parse_line(line: &str) -> (Root, Root) {
        let mut split = line.split(": ");
        let _throwaway = split.next().unwrap();
        let useful_part = split.next().unwrap();

        let mut split = useful_part.split(" - ");
        let starting = split.next().unwrap();
        let expected = split.next().unwrap();
        let starting = parse::binary::from_str(starting).unwrap();
        let expected = parse::binary::from_str(expected).unwrap();
        (starting.into(), expected.into())
    }

    pub fn reduce_with_timeout(
        term: &Root,
        visit_order: VisitOrder,
        timeout: Option<Duration>,
    ) -> (Option<ReductionResult>, Duration) {
        let mut reducer = Reducer::new(term.clone(), visit_order);
        let now = Instant::now();
        loop {
            if let Some(value) = reducer.reduce_one() {
                return (Some(value), now.elapsed());
            }
            if let Some(timeout) = timeout
                && now.elapsed() > timeout
            {
                return (None, now.elapsed());
            }
        }
    }
}
