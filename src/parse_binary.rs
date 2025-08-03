use crate::{debruijn::Debruijn, parse_debruijn};
use std::str::FromStr;

struct BinaryTokenStream {
    bits: Vec<bool>,
    i: usize,
}

impl BinaryTokenStream {
    fn has_next(&self) -> bool {
        self.i < self.bits.len()
    }
    fn next(&mut self) -> Option<bool> {
        if self.has_next() {
            let bit = self.bits[self.i];
            self.i += 1;
            Some(bit)
        } else {
            None
        }
    }

    fn parse(&mut self) -> Result<Debruijn, ParseError> {
        match self.next() {
            // 00 and 01
            Some(false) => match self.next() {
                // Abstraction: blc(λM) = 00 blc(M)
                Some(false) => Ok(Debruijn::Abstraction {
                    body: Box::new(self.parse()?),
                }),
                // Application = blc(M N) = 01 blc(M) blc(N)
                Some(true) => Ok(Debruijn::Application {
                    func: Box::new(self.parse()?),
                    arg: Box::new(self.parse()?),
                }),
                None => Err(ParseError::EOF),
            },
            // 1_i0
            // Index: blc(i) = 1i0
            Some(true) => {
                // already consumed one 1-bit
                let mut index = 1;
                loop {
                    match self.next() {
                        Some(true) => index += 1,
                        Some(false) => return Ok(Debruijn::Index(index)),
                        None => return Err(ParseError::EOF),
                    }
                }
            }
            None => Err(ParseError::EOF),
        }
    }
}

impl FromStr for BinaryTokenStream {
    type Err = !;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let bits = s
            .chars()
            .filter_map(|c| match c {
                '0' => Some(false),
                '1' => Some(true),
                _ => None,
            })
            .collect();
        Ok(BinaryTokenStream { bits, i: 0 })
    }
}

#[derive(Debug)]
pub enum ParseError {
    EOF,
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::{debruijn::Debruijn, parse_binary::BinaryTokenStream};

    #[test]
    fn parse_universal_machine() {
        let binary = "
        01 01 00 01 10 10 00 00 00 01 01 01 10 00 00 00 00 01 1110 00 01 01 111110 01 1110 
        00 01 01 110 01 1110 00 00 01 1110 00 01 01 10 110 1110 01 11110 00 01 11110 00 
        01 01 1110 10 01 110 10 01 01 10 01 110 00 01 10 110 00 01 01 11110 00 01 11110 00
        01 110 01 10 11110 111110 01 1110 1110 110 00 01 10 01 00 01 10 10 00 01 10 10  
        00 1110 01 10 11110 111110 01 1110 1110 110 00 01 10 01 00 01 10 10 00 01 10 10";

        let expected =
            "(λ 1 1)(λλλ 1 (λλλλ 3 (λ 5 (3 (λ 2 (3 (λλ 3 (λ 1 2 3)))(4 (λ 4 (λ3 1 (2 1))))))
        (1 (2 (λ1 2))(λ4 (λ4 (λ2 (1 4))) 5)))) (3 3) 2)(λ 1 ((λ 1 1)(λ 1 1)))";
        let expected = Debruijn::from_str(expected).unwrap();

        let mut actual = BinaryTokenStream::from_str(binary).unwrap();
        let actual = actual.parse().unwrap();

        assert_eq!(expected, actual);
    }
}
