#![feature(iter_intersperse)]

use std::fmt::Display;

/// A literal
/// TODO: This should eventually become more sophisticated, possibly containing
/// references to some manager struct that knows about all literals. For now, this can
/// just be a string
#[derive(Debug, Clone, PartialEq, Eq)]
struct Literal(String);
impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<&str> for Literal {
    fn from(value: &str) -> Self {
        Literal(value.to_string())
    }
}

impl From<String> for Literal {
    fn from(value: String) -> Self {
        Literal(value)
    }
}

/// A term in the lambda calculus.
#[derive(Debug, PartialEq, Eq)]
enum Term {
    Literal(Literal),
    Abstraction(Literal, Box<Term>),
    Application(Box<Term>, Box<Term>),
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Literal(literal) => write!(f, "{}", literal.0),
            Term::Abstraction(literal, term) => write!(f, "(λ {} . {})", literal, term),
            Term::Application(term1, term2) => write!(f, "({} {})", term1, term2),
        }
    }
}

// Helper method to create a Literal
fn lit(lit: impl Into<Literal>) -> Term {
    Term::Literal(lit.into())
}

// Helper method to create a lambda abstraction
fn def(input: impl Into<Literal>, term: Term) -> Term {
    Term::Abstraction(input.into(), Box::new(term))
}

// Helper method to create a function application
fn call(term1: Term, term2: Term) -> Term {
    Term::Application(Box::new(term1), Box::new(term2))
}

/// Tokenize a lambda calculus expression into a series of Tokens
fn tokenize(expr: &str) -> Vec<Token> {
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
    return tokens;
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
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

fn pretty(tokens: &[Token]) -> String {
    tokens
        .iter()
        .map(|token| format!("{}", token))
        .intersperse(" ".to_string())
        .collect()
}

/// A stream of tokens
struct TokenStream<'a> {
    tokens: &'a [Token],
    // Current position in the stream
    index: usize,
}

impl<'a> TokenStream<'a> {
    /// Create a new TokenStream from the given slice of tokens
    fn new(tokens: &'a [Token]) -> Self {
        Self { tokens, index: 0 }
    }

    /// Return the next token in the stream without consuming it
    fn peek(&self) -> Option<Token> {
        self.tokens.get(self.index).cloned()
    }

    /// Consume the given token. If the next token does not match `expected`, then it is not consumed
    /// and a ParseError is returned instead.
    fn consume_one(&mut self, expected: Token) -> Result<(), ParseError> {
        let actual = self.peek();
        if actual == Some(expected.clone()) {
            self.index += 1;
            Ok(())
        } else {
            Err(ParseError::expected_token(expected, actual))
        }
    }

    /// Consume the next token. If the next token is not a Litearl, then it is not consumed
    /// and a ParseError is returned instead
    fn consume_literal(&mut self) -> Result<String, ParseError> {
        let actual = self.peek();
        if let Some(Token::Literal(literal)) = actual {
            self.index += 1;
            Ok(literal)
        } else {
            Err(ParseError::expected_literal(actual))
        }
    }

    /// Get the remaining list of Tokens in the stream. This does not consume the tokens.
    fn remaining(&self) -> Vec<Token> {
        self.tokens[self.index..].to_vec()
    }
}

fn parse_program(tokens: &mut TokenStream) -> Result<Term, ParseError> {
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
    Ok(lit(tokens.consume_literal()?))
}

fn parse_call(tokens: &mut TokenStream) -> Result<Term, ParseError> {
    tokens.consume_one(Token::LeftParen)?;
    let term1 = parse_term(tokens)?;
    let term2 = parse_term(tokens)?;
    tokens.consume_one(Token::RightParen)?;
    Ok(call(term1, term2))
}

fn parse_lambda(tokens: &mut TokenStream) -> Result<Term, ParseError> {
    tokens.consume_one(Token::Lambda)?;
    let literal = tokens.consume_literal()?;
    tokens.consume_one(Token::Dot)?;
    let term = parse_term(tokens)?;
    Ok(def(literal, term))
}

#[derive(Debug, PartialEq, Eq)]
enum ParseError {
    UnexpectedToken {
        expected: Vec<Token>,
        actual: Option<Token>,
    },
    LeftoverTokens(Vec<Token>),
}

impl ParseError {
    fn expected_literal(actual: Option<Token>) -> ParseError {
        ParseError::UnexpectedToken {
            expected: vec![Token::Literal("expected a literal".to_string())],
            actual,
        }
    }

    fn expected_token(expected: Token, actual: Option<Token>) -> ParseError {
        ParseError::UnexpectedToken {
            expected: vec![expected],
            actual,
        }
    }

    fn expected_tokens(actual: Option<Token>) -> ParseError {
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

fn foo(program: &str) {
    println!("RAW   : {}", program);
    let tokens = tokenize(program);
    println!("TOKENS: {}", pretty(&tokens));
    let mut token_stream = TokenStream::new(&tokens);
    match parse_program(&mut token_stream) {
        Ok(program) => println!("PARSED: {}", program),
        Err(err) => println!("ERROR : {:?}", err),
    }
    println!("--------")
}

fn main() {
    let lambda = call(def("x", lit("x")), lit("y"));
    println!("{}", lambda);
    let lambda = def("x", call(lit("x"), lit("y")));
    println!("{}", lambda);
    println!("----");
    foo("(λx.x y)");

    foo("λx.x y");
    foo("λx.λy.x");
    foo("λx.λy.(x y)");
}
#[cfg(test)]
mod tests {
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
        let expected = def("x", lit("x"));
        assert_parse(input, expected);
    }

    #[test]
    fn test_parse_simple_call() {
        let input = "(x y)";
        let expected = call(lit("x"), lit("y"));
        assert_parse(input, expected);
    }

    #[test]
    fn test_parse_multiletter_literal() {
        let input = "(λfoo.bar baz)";
        let expected = call(def("foo", lit("bar")), lit("baz"));
        assert_parse(input, expected);
    }

    #[test]
    fn test_parse_nested_lambda() {
        let input = "λa.λb.λc.((a b) c)";
        let expected = def(
            "a",
            def("b", def("c", call(call(lit("a"), lit("b")), lit("c")))),
        );
        assert_parse(input, expected);
    }

    #[test]
    fn test_parse_invalid_lambda() {
        assert_invalid("λa.λb.λc.");
    }

    #[test]
    fn test_parse_invalid_call() {
        assert_invalid("(a b (c d))");
    }

    #[test]
    fn test_parse_invalid_lambda2() {
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
