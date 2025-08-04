/// Xorshift128+ implementation stolen from tiny-rng
/// https://docs.rs/tiny-rng/
pub struct Rng {
    state: (u64, u64),
}

impl Rng {
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
