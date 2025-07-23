use std::fmt::Display;

use crate::term::{Literal, Term};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    LeftParen,
    RightParen,
    Lambda,
    Dot,
    Literal(String),
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::LeftParen => write!(f, "("),
            Token::RightParen => write!(f, ")"),
            Token::Lambda => write!(f, "λ"),
            Token::Dot => write!(f, "."),
            Token::Literal(s) => write!(f, "{}", s),
        }
    }
}

pub fn tokenize(expr: &str) -> Vec<Token> {
    let mut tokens = vec![];
    let mut string = String::new();
    for char in expr.chars() {
        let (cut_string, push_token) = match char {
            'λ' => (true, Some(Token::Lambda)),
            '.' => (true, Some(Token::Dot)),
            '(' => (true, Some(Token::LeftParen)),
            ')' => (true, Some(Token::RightParen)),
            ' ' => (true, None),
            _ => (false, None),
        };

        if cut_string {
            if !string.is_empty() {
                tokens.push(Token::Literal(string.clone()));
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
        tokens.push(Token::Literal(string));
    }
    tokens
}

pub fn pretty(tokens: &[Token]) -> String {
    tokens
        .iter()
        .map(|token| format!("{}", token))
        .intersperse(" ".to_string())
        .collect()
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

    pub fn consume_one(&mut self, expected: Token) -> Result<(), ParseError> {
        let actual = self.peek();
        if actual == Some(expected.clone()) {
            self.index += 1;
            Ok(())
        } else {
            Err(ParseError::expected_token(expected, actual))
        }
    }

    pub fn consume_literal(&mut self) -> Result<String, ParseError> {
        let actual = self.peek();
        if let Some(Token::Literal(literal)) = actual {
            self.index += 1;
            Ok(literal)
        } else {
            Err(ParseError::expected_literal(actual))
        }
    }

    pub fn remaining(&self) -> Vec<Token> {
        self.tokens[self.index..].to_vec()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    UnexpectedToken {
        expected: Vec<Token>,
        actual: Option<Token>,
    },
    LeftoverTokens(Vec<Token>),
}

impl ParseError {
    pub fn expected_literal(actual: Option<Token>) -> ParseError {
        ParseError::UnexpectedToken {
            expected: vec![Token::Literal("expected a literal".to_string())],
            actual,
        }
    }

    pub fn expected_token(expected: Token, actual: Option<Token>) -> ParseError {
        ParseError::UnexpectedToken {
            expected: vec![expected],
            actual,
        }
    }

    pub fn expected_tokens(actual: Option<Token>) -> ParseError {
        ParseError::UnexpectedToken {
            expected: vec![
                Token::Lambda,
                Token::LeftParen,
                Token::Literal("literal".to_string()),
            ],
            actual,
        }
    }
}

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
            ParseError::LeftoverTokens(tokens) => {
                write!(
                    f,
                    "Leftover tokens after parsing: [{}]",
                    tokens
                        .iter()
                        .map(|t| format!("{}", t))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

pub fn parse_program(tokens: &mut TokenStream) -> Result<Term, ParseError> {
    let term = parse_term(tokens)?;
    let remaining = tokens.remaining();
    if !remaining.is_empty() {
        Err(ParseError::LeftoverTokens(remaining))
    } else {
        Ok(term)
    }
}

fn parse_term(tokens: &mut TokenStream) -> Result<Term, ParseError> {
    match tokens.peek() {
        Some(token) => match token {
            Token::Literal(_) => parse_literal(tokens),
            Token::LeftParen => parse_call(tokens),
            Token::Lambda => parse_lambda(tokens),
            Token::Dot | Token::RightParen => Err(ParseError::expected_tokens(Some(token))),
        },
        None => Err(ParseError::expected_tokens(None)),
    }
}

fn parse_literal(tokens: &mut TokenStream<'_>) -> Result<Term, ParseError> {
    Ok(Term::Literal(Literal(tokens.consume_literal()?)))
}

fn parse_call(tokens: &mut TokenStream) -> Result<Term, ParseError> {
    tokens.consume_one(Token::LeftParen)?;
    let term1 = parse_term(tokens)?;
    let term2 = parse_term(tokens)?;
    tokens.consume_one(Token::RightParen)?;
    Ok(Term::Application(Box::new(term1), Box::new(term2)))
}

fn parse_lambda(tokens: &mut TokenStream) -> Result<Term, ParseError> {
    tokens.consume_one(Token::Lambda)?;
    let literal = tokens.consume_literal()?;
    tokens.consume_one(Token::Dot)?;
    let term = parse_term(tokens)?;
    Ok(Term::Abstraction(Literal(literal), Box::new(term)))
}

#[cfg(test)]
mod tests {
    use crate::{call, def, lit};

    use super::*;

    fn assert_parse(input: &str, expected: Term) {
        let tokens = tokenize(input);
        let mut stream = TokenStream::new(&tokens);
        let actual = parse_program(&mut stream).unwrap();
        assert_eq!(expected, actual);
    }

    fn assert_invalid(input: &str) {
        let tokens = tokenize(input);
        let mut stream = TokenStream::new(&tokens);
        let actual = parse_program(&mut stream);
        assert!(actual.is_err());
    }

    #[test]
    fn test_tokenize_simple_lambda() {
        let input = "λx.x";
        let tokens = tokenize(input);
        let expected = vec![
            Token::Lambda,
            Token::Literal("x".to_string()),
            Token::Dot,
            Token::Literal("x".to_string()),
        ];
        assert_eq!(tokens, expected);
    }

    #[test]
    fn test_tokenize_application() {
        let input = "(λx.x y)";
        let tokens = tokenize(input);
        let expected = vec![
            Token::LeftParen,
            Token::Lambda,
            Token::Literal("x".to_string()),
            Token::Dot,
            Token::Literal("x".to_string()),
            Token::Literal("y".to_string()),
            Token::RightParen,
        ];
        assert_eq!(tokens, expected);
    }

    #[test]
    fn test_tokenize_nested_lambda() {
        let input = "λx.λy.(x y)";
        let tokens = tokenize(input);
        let expected = vec![
            Token::Lambda,
            Token::Literal("x".to_string()),
            Token::Dot,
            Token::Lambda,
            Token::Literal("y".to_string()),
            Token::Dot,
            Token::LeftParen,
            Token::Literal("x".to_string()),
            Token::Literal("y".to_string()),
            Token::RightParen,
        ];
        assert_eq!(tokens, expected);
    }

    #[test]
    fn test_tokenize_with_spaces() {
        let input = " ( λ x . x y ) ";
        let tokens = tokenize(input);
        let expected = vec![
            Token::LeftParen,
            Token::Lambda,
            Token::Literal("x".to_string()),
            Token::Dot,
            Token::Literal("x".to_string()),
            Token::Literal("y".to_string()),
            Token::RightParen,
        ];
        assert_eq!(tokens, expected);
    }

    #[test]
    fn test_parse_simple_literal() {
        let input = "x";
        let expected = lit("x");
        assert_parse(input, expected);
    }

    #[test]
    fn test_parse_simple_lambda() {
        let input = "λx.x";
        let expected = def("x", "x");
        assert_parse(input, expected);
    }

    #[test]
    fn test_parse_simple_call() {
        let input = "(x y)";
        let expected = call("x", "y");
        assert_parse(input, expected);
    }

    #[test]
    fn test_parse_multiletter_literal() {
        let input = "(λfoo.bar baz)";
        let expected = call(def("foo", "bar"), "baz");
        assert_parse(input, expected);
    }

    #[test]
    fn test_parse_nested_lambda() {
        let input = "λa.λb.λc.((a b) c)";
        let expected = def("a", def("b", def("c", call(call("a", "b"), "c"))));
        assert_parse(input, expected);
    }

    #[test]
    fn test_parse_invalid_lambda() {
        assert_invalid("λa.λb.λc.");
    }

    #[test]
    fn test_parse_invalid_lambda_missing_dot() {
        assert_invalid("λ a b");
    }

    #[test]
    fn test_parse_invalid_leftovers() {
        assert_invalid("λa.b leftover");
    }

    #[test]
    fn test_parse_invalid_dot() {
        assert_invalid(". λa.b");
    }

    #[test]
    fn test_parse_invalid_paren() {
        assert_invalid(") λa.b");
    }

    #[test]
    fn test_parse_invalid_lambda_argument() {
        assert_invalid("λ(a b).c");
    }
}
