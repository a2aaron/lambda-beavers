use std::fmt::Display;

use crate::term::{self, Term};

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
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    UnexpectedToken {
        expected: Vec<Token>,
        actual: Option<Token>,
    },
    Empty,
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

    pub fn expected_tokens(actual: Token) -> ParseError {
        ParseError::UnexpectedToken {
            expected: vec![
                Token::Lambda,
                Token::LeftParen,
                Token::RightParen,
                Token::Literal("literal".to_string()),
            ],
            actual: Some(actual),
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
            ParseError::Empty => write!(f, "End of line too early"),
        }
    }
}

pub fn parse_program(tokens: &[Token]) -> Result<Term, ParseError> {
    if tokens.is_empty() {
        return Err(ParseError::Empty);
    }

    // Strip off first and last tokens if they are both parens
    let tokens = if tokens[0] == Token::LeftParen && tokens[tokens.len() - 1] == Token::RightParen {
        &tokens[1..tokens.len() - 1]
    } else {
        tokens
    };

    let mut tokens = TokenStream::new(tokens);
    let term = parse_term_up_to_paren(&mut tokens)?;
    Ok(term)
}

fn parse_term_up_to_paren(tokens: &mut TokenStream) -> Result<Term, ParseError> {
    fn wrap(current_term: Option<Term>, term: Term) -> Option<Term> {
        if let Some(term1) = current_term {
            return Some(term::call(term1, term));
        } else {
            return Some(term);
        }
    }

    let mut current_term: Option<Term> = None;
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
                let arg = tokens.consume_literal()?;
                tokens.consume_one(Token::Dot)?;
                let body = parse_term_up_to_paren(tokens)?;
                let term = term::def(arg, body);
                current_term = wrap(current_term, term);
            }
            Token::Literal(_) => {
                let literal = tokens.consume_literal().unwrap();
                let term = term::lit(literal);
                current_term = wrap(current_term, term);
            }
            Token::RightParen => break,
            Token::Dot => return Err(ParseError::expected_tokens(token)),
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
    use crate::{call, def, lit};

    use super::*;

    macro_rules! assert_parse {
        ($input:expr, $expected:expr) => {{
            let tokens = tokenize($input);
            let actual = parse_program(&tokens).unwrap();
            assert_eq!($expected, actual);
        }};
    }

    macro_rules! assert_invalid {
        ($input:expr) => {{
            let tokens = tokenize($input);
            let actual = parse_program(&tokens);
            assert!(actual.is_err());
        }};
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
        assert_parse!(input, expected);
    }

    #[test]
    fn test_parse_simple_lambda() {
        let input = "λx.x";
        let expected = def("x", "x");
        assert_parse!(input, expected);
    }

    #[test]
    fn test_parse_simple_call() {
        let input = "(x y)";
        let expected = call("x", "y");
        assert_parse!(input, expected);
    }

    #[test]
    fn test_parse_multiletter_literal() {
        let input = "(λfoo.bar baz)";
        let expected = def("foo", call("bar", "baz"));
        assert_parse!(input, expected);
    }

    #[test]
    fn test_parse_nested_lambda() {
        let input = "λa.λb.λc.((a b) c)";
        let expected = def("a", def("b", def("c", call(call("a", "b"), "c"))));
        assert_parse!(input, expected);
    }

    #[test]
    fn test_parse_drop_outer_parens1() {
        assert_parse!("a", lit("a"));
    }

    #[test]
    fn test_parse_drop_outer_parens2() {
        assert_parse!("a b", call("a", "b"));
    }

    #[test]
    fn test_parse_drop_outer_parens3() {
        assert_parse!("λa.a", def("a", "a"));
    }

    #[test]
    fn test_parse_left_associative() {
        assert_parse!("a b c", call(call("a", "b"), "c"));
    }

    #[test]
    fn test_parse_lambda_greedy_extend() {
        assert_parse!("λx.M N", def("x", call("M", "N")));
    }

    #[test]
    fn test_parse_invalid_empty() {
        assert_invalid!("");
    }

    #[test]
    fn test_parse_invalid_lambda_missing_body() {
        assert_invalid!("λa.λb.λc.");
    }

    #[test]
    fn test_parse_invalid_lambda_missing_dot() {
        assert_invalid!("λ a b");
    }

    #[test]
    fn test_parse_valid_leftovers() {
        assert_parse!("λa.b leftover", def("a", call("b", "leftover")));
    }

    #[test]
    fn test_parse_invalid_dot() {
        assert_invalid!(". λa.b");
    }

    #[test]
    fn test_parse_invalid_paren() {
        assert_invalid!(") λa.b");
    }

    #[test]
    fn test_parse_mismatched_paren() {
        assert_invalid!("(λa.b");
    }

    #[test]
    fn test_parse_invalid_lambda_argument() {
        assert_invalid!("λ(a b).c");
    }
}
