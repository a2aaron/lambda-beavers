use crate::debruijn::Debruijn;
use core::fmt;
use std::{fmt::Display, str::FromStr};

type ParseResult<T> = Result<T, ParseError>;

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

    fn parse(&mut self) -> ParseResult<Debruijn> {
        let term = self._parse()?;
        if self.has_next() {
            Err(ParseError::LeftoverInput)
        } else {
            Ok(term)
        }
    }

    fn _parse(&mut self) -> ParseResult<Debruijn> {
        match self.next() {
            // 00 and 01
            Some(false) => match self.next() {
                // Abstraction: blc(λM) = 00 blc(M)
                Some(false) => Ok(Debruijn::Abstraction {
                    body: Box::new(self._parse()?),
                }),
                // Application = blc(M N) = 01 blc(M) blc(N)
                Some(true) => Ok(Debruijn::Application {
                    func: Box::new(self._parse()?),
                    arg: Box::new(self._parse()?),
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

impl Display for BinaryTokenStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bits: String = self
            .bits
            .iter()
            .map(|bit| if *bit { '1' } else { '0' })
            .collect();
        writeln!(f, "{bits}")?;
        for idx in 0..self.bits.len() {
            if idx == self.i {
                write!(f, "^")?;
            } else {
                write!(f, " ")?;
            }
        }
        Ok(())
    }
}

impl From<Vec<bool>> for BinaryTokenStream {
    fn from(bits: Vec<bool>) -> Self {
        BinaryTokenStream { bits, i: 0 }
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

pub fn from_vec(bits: Vec<bool>) -> ParseResult<Debruijn> {
    BinaryTokenStream::from(bits).parse()
}

pub fn from_str(string: &str) -> ParseResult<Debruijn> {
    BinaryTokenStream::from_str(string).unwrap().parse()
}

#[derive(Debug)]
pub enum ParseError {
    EOF,
    LeftoverInput,
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::{
        debruijn::Debruijn,
        parse_binary::{self, BinaryTokenStream},
        term::Term,
    };

    #[test]
    fn parse_universal_machine() {
        let binary = "
        01 01 00 01 10 10 00 00 00 01 01 01 10 00 00 00 00 01 1110 00 01 01 111110 01 1110 
        00 01 01 110 01 1110 00 00 01 1110 00 01 01 10 110 1110 01 11110 00 01 11110 00 
        01 01 1110 10 01 110 10 01 01 10 01 110 00 01 10 110 00 01 01 11110 00 01 11110 00
        01110 01 10 11110 111110 01 1110 1110 110 00 01 10 01 00 01 10 10 00 01 10 10";

        let expected =
            "(λ 1 1)(λλλ 1 (λλλλ 3 (λ 5 (3 (λ 2 (3 (λλ 3 (λ 1 2 3)))(4 (λ 4 (λ3 1 (2 1))))))
        (1 (2 (λ1 2))(λ4 (λ4 (λ2 (1 4))) 5)))) (3 3) 2)(λ 1 ((λ 1 1)(λ 1 1)))";
        let expected = Debruijn::from_str(expected).unwrap();

        let mut stream = BinaryTokenStream::from_str(binary).unwrap();
        let parse = stream.parse();
        println!("{}", stream);
        let actual = parse.unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_omega() {
        let term_classic = Term::from_str("(λx.x x)(λx.x x)").unwrap();
        let term_classic = Debruijn::try_from(term_classic).unwrap();

        let term_debruijn = Debruijn::from_str("(λ 1 1)(λ 1 1)").unwrap();

        let term_binary = parse_binary::from_str("01 00 10 10 00 10 10").unwrap();

        assert_eq!(term_classic, term_debruijn);
        assert_eq!(term_debruijn, term_binary);
    }
}
