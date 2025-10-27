use std::{error::Error, fmt::Display, num::ParseIntError};

use crate::debruijn::{self, Debruijn};

pub type ParseResult<T> = Result<T, ParseError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    LeftParen,
    RightParen,
    Lambda,
    Index(usize),
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::LeftParen => write!(f, "("),
            Token::RightParen => write!(f, ")"),
            Token::Lambda => write!(f, "λ"),
            Token::Index(index) => write!(f, "{}", index),
        }
    }
}

pub fn tokenize(term: &str) -> ParseResult<Vec<Token>> {
    fn try_tokenize_int(string: &str) -> ParseResult<usize> {
        match string.parse::<usize>() {
            Ok(int) => Ok(int),
            Err(err) => Err(ParseError::ParseIntError {
                err,
                token: string.to_string(),
            }),
        }
    }

    let mut tokens = vec![];
    let mut string = String::new();
    for char in term.chars() {
        let (cut_string, push_token) = match char {
            'λ' | 'y' | '\\' => (true, Some(Token::Lambda)),
            '(' => (true, Some(Token::LeftParen)),
            ')' => (true, Some(Token::RightParen)),
            c if c.is_whitespace() => (true, None),
            _ => (false, None),
        };

        if cut_string {
            if !string.is_empty() {
                let index = try_tokenize_int(&string)?;
                tokens.push(Token::Index(index));
                string.clear();
            }
        } else {
            string.push(char);
        }

        if let Some(token) = push_token {
            tokens.push(token);
        }
    }

    if !string.is_empty() {
        let index = try_tokenize_int(&string)?;
        tokens.push(Token::Index(index));
    }
    Ok(tokens)
}

pub struct TokenStream<'a> {
    pub tokens: &'a [Token],
    pub index: usize,
}

impl<'a> TokenStream<'a> {
    pub fn new(tokens: &'a [Token]) -> Self {
        Self { tokens, index: 0 }
    }

    pub fn peek(&self) -> Option<Token> {
        self.tokens.get(self.index).cloned()
    }

    pub fn consume_one(&mut self, expected: Token) -> ParseResult<()> {
        let actual = self.peek();
        if actual == Some(expected.clone()) {
            self.index += 1;
            Ok(())
        } else {
            Err(ParseError::expected_token(expected, actual))
        }
    }

    pub fn consume_index(&mut self) -> ParseResult<usize> {
        let actual = self.peek();
        if let Some(Token::Index(index)) = actual {
            self.index += 1;
            Ok(index)
        } else {
            Err(ParseError::expected_index(actual))
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    UnexpectedToken {
        expected: Vec<Token>,
        actual: Option<Token>,
    },
    ParseIntError {
        err: ParseIntError,
        token: String,
    },
    IntIsZeroError,
    Empty,
}

impl ParseError {
    fn expected_index(actual: Option<Token>) -> ParseError {
        ParseError::UnexpectedToken {
            expected: vec![Token::Index(0)],
            actual,
        }
    }

    fn expected_token(expected: Token, actual: Option<Token>) -> ParseError {
        ParseError::UnexpectedToken {
            expected: vec![expected],
            actual,
        }
    }
}

impl Error for ParseError {}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::UnexpectedToken { expected, actual } => {
                write!(
                    f,
                    "Unexpected token. Expected one of: [{}], but found: {}",
                    expected
                        .iter()
                        .map(|t| format!("{}", t))
                        .collect::<Vec<_>>()
                        .join(", "),
                    match actual {
                        Some(token) => format!("{}", token),
                        None => "end of input".to_string(),
                    }
                )
            }
            ParseError::Empty => write!(f, "End of line too early"),
            ParseError::ParseIntError { err, token } => {
                write!(f, "Couldn't parse {} as integer: {}", token, err)
            }
            ParseError::IntIsZeroError => write!(f, "Integer must be non-zero"),
        }
    }
}

pub fn parse_program(tokens: &[Token]) -> ParseResult<Debruijn> {
    if tokens.is_empty() {
        return Err(ParseError::Empty);
    }

    let mut tokens = TokenStream::new(tokens);
    let term = parse_term_up_to_paren(&mut tokens)?;
    Ok(term)
}

fn parse_term_up_to_paren(tokens: &mut TokenStream) -> ParseResult<Debruijn> {
    fn wrap(current_term: Option<Debruijn>, term: Debruijn) -> Option<Debruijn> {
        if let Some(term1) = current_term {
            return Some(debruijn::call(term1, term));
        } else {
            return Some(term);
        }
    }

    let mut current_term: Option<Debruijn> = None;
    while let Some(token) = tokens.peek() {
        match token {
            Token::LeftParen => {
                tokens.consume_one(Token::LeftParen).unwrap();
                let term = parse_term_up_to_paren(tokens)?;
                tokens.consume_one(Token::RightParen)?;
                current_term = wrap(current_term, term);
            }
            Token::Lambda => {
                tokens.consume_one(Token::Lambda).unwrap();
                let body = parse_term_up_to_paren(tokens)?;
                let term = debruijn::def(body);
                current_term = wrap(current_term, term);
            }
            Token::Index(_index) => {
                let index = tokens.consume_index().unwrap();
                if index == 0 {
                    return Err(ParseError::IntIsZeroError);
                }
                let term = debruijn::idx(index);
                current_term = wrap(current_term, term);
            }
            Token::RightParen => break,
        }
    }
    if let Some(current_term) = current_term {
        Ok(current_term)
    } else {
        Err(ParseError::Empty)
    }
}

#[cfg(test)]
mod tests {
    use crate::debruijn::{def, idx};

    use super::*;
    macro_rules! assert_parse {
        ($input:expr, $expected:expr) => {{
            let tokens = tokenize($input).unwrap();
            let actual = parse_program(&tokens).unwrap();
            let expected = Debruijn::from($expected);
            assert_eq!(expected, actual);
        }};
    }

    macro_rules! assert_invalid {
        ($input:expr) => {{
            let tokens = tokenize($input).unwrap();
            let actual = parse_program(&tokens);
            assert!(actual.is_err());
        }};
    }

    #[test]
    fn tokenize_simple_lambda() {
        let input = "λ 1";
        let tokens = tokenize(input).unwrap();
        let expected = vec![Token::Lambda, Token::Index(1)];
        assert_eq!(tokens, expected);
    }

    #[test]
    fn tokenize_application() {
        let input = "(λ 1 2)";
        let tokens = tokenize(input).unwrap();
        let expected = vec![
            Token::LeftParen,
            Token::Lambda,
            Token::Index(1),
            Token::Index(2),
            Token::RightParen,
        ];
        assert_eq!(tokens, expected);
    }

    #[test]
    fn tokenize_nested_lambda() {
        let input = "λλ (1 2)";
        let tokens = tokenize(input).unwrap();
        let expected = vec![
            Token::Lambda,
            Token::Lambda,
            Token::LeftParen,
            Token::Index(1),
            Token::Index(2),
            Token::RightParen,
        ];
        assert_eq!(tokens, expected);
    }

    #[test]
    fn tokenize_with_spaces() {
        let input = " ( λ 1 2 ) ";
        let tokens = tokenize(input).unwrap();
        let expected = vec![
            Token::LeftParen,
            Token::Lambda,
            Token::Index(1),
            Token::Index(2),
            Token::RightParen,
        ];
        assert_eq!(tokens, expected);
    }

    #[test]
    fn parse_simple_literal() {
        assert_parse!("1", idx(1));
    }

    #[test]
    fn parse_simple_lambda() {
        assert_parse!("(λ 1)", def(1));
    }

    #[test]
    fn parse_simple_call() {
        assert_parse!("(1 2)", (1, 2));
    }

    #[test]
    fn parse_nested_lambda() {
        assert_parse!("λ λ λ ((3 2) 1)", def(def(def(((3, 2), 1)))));
    }

    #[test]
    fn parse_drop_outer_parens2() {
        assert_parse!("1 2", (1, 2));
    }

    #[test]
    fn parse_drop_outer_parens3() {
        assert_parse!("λ 1", def(1));
    }

    #[test]
    fn parse_left_associative() {
        assert_parse!("1 2 3", ((1, 2), 3));
    }

    #[test]
    fn parse_lambda_greedy_extend() {
        assert_parse!("λ 1 2", def((1, 2)));
    }

    #[test]
    fn parse_invalid_empty() {
        assert_invalid!("");
    }

    #[test]
    fn parse_zero_is_invalid() {
        assert_invalid!("λ 0");
    }

    #[test]
    fn parse_invalid_lambda_missing_body() {
        assert_invalid!("λ λ λ");
    }

    #[test]
    fn parse_invalid_paren() {
        assert_invalid!(") λ 2");
    }

    #[test]
    fn parse_mismatched_paren() {
        assert_invalid!("(λ 2");
    }

    #[test]
    fn parse_and_false() {
        assert_parse!("(λ λ 2 1 2) (λ λ 1)", (def(def(((2, 1), 2))), def(def(1))));
    }

    #[test]
    fn parse_and() {
        assert_parse!("λ λ 2 1 2", def(def(((2, 1), 2))));
    }

    #[test]
    fn parse_false() {
        assert_parse!("λ λ 1", def(def(1)));
    }

    #[test]
    fn pretty_print_roundtrip() {}
}
