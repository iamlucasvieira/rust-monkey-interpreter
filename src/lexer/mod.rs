use crate::token;
use log::debug;

/// Lexer is a struct that holds the state of the lexer.
pub struct Lexer<'a> {
    input_chars: std::str::Chars<'a>,
    ch: Option<char>,
    peek: Option<char>,
}

impl<'a> Lexer<'a> {
    /// Returns the next token from the input.
    pub fn new(input: &'a str) -> Lexer {
        let mut l = Lexer {
            input_chars: input.chars(),
            ch: None,
            peek: None,
        };
        l.read_char();
        l.read_char();
        l
    }

    /// Returns the next token from the input.
    fn read_char(&mut self) {
        self.ch = self.peek;
        self.peek = self.input_chars.next();
    }

    /// Returns the next token from the input.
    pub fn next_token(&mut self) -> token::Token {
        debug!("Getting next token");
        self.skip_whitespace();

        let tok = match self.ch {
            Some(ch) if is_letter(ch) => {
                let identifier = self.read_identifier();
                token::Token::from_keyword(&identifier)
            }
            Some(ch) if is_digit(ch) => {
                let number = self.read_number();
                token::Token::INT(number)
            }
            Some('=') => {
                if self.peek == Some('=') {
                    self.read_char();
                    token::Token::EQ
                } else {
                    token::Token::ASSIGN
                }
            }
            Some('!') => {
                if self.peek == Some('=') {
                    self.read_char();
                    token::Token::NOTEQ
                } else {
                    token::Token::BANG
                }
            }
            Some('"') => {
                let string = self.read_string();
                token::Token::STRING(string)
            }
            Some(ch) => token::Token::from_literal(&ch.to_string()),
            None => token::Token::EOF,
        };

        self.read_char();

        tok
    }

    /// Reads an identifier from the input.
    fn read_identifier(&mut self) -> String {
        if let Some(ch) = self.ch {
            if !is_letter(ch) {
                return "".to_string();
            }
        }

        let mut identifier = Vec::new();
        while let Some(ch) = self.ch {
            identifier.push(ch);
            if let Some(peek) = self.peek {
                if is_letter(peek) {
                    self.read_char();
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        identifier.iter().collect()
    }

    fn read_number(&mut self) -> String {
        if let Some(ch) = self.ch {
            if !is_digit(ch) {
                return "".to_string();
            }
        }

        let mut number = Vec::new();
        while let Some(ch) = self.ch {
            number.push(ch);
            if let Some(peek) = self.peek {
                if is_digit(peek) {
                    self.read_char();
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        number.iter().collect()
    }

    fn read_string(&mut self) -> String {
        let mut string = Vec::new();
        self.read_char();
        while let Some(ch) = self.ch {
            if ch == '"' || ch == '\0' {
                break;
            }
            string.push(ch);
            self.read_char();
        }
        string.iter().collect()
    }

    /// Skips whitespace characters.
    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.ch {
            if ch.is_whitespace() {
                self.read_char();
            } else {
                break;
            }
        }
    }
}

fn is_letter(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

fn is_digit(ch: char) -> bool {
    ch.is_ascii_digit()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_next_token() {
        let input = String::from("=+(){},;");

        struct TestCase<'a> {
            expected_type: token::Token,
            expected_literal: &'a str,
        }

        let test_cases = vec![
            TestCase {
                expected_type: token::Token::ASSIGN,
                expected_literal: "=",
            },
            TestCase {
                expected_type: token::Token::PLUS,
                expected_literal: "+",
            },
            TestCase {
                expected_type: token::Token::LPAREN,
                expected_literal: "(",
            },
            TestCase {
                expected_type: token::Token::RPAREN,
                expected_literal: ")",
            },
            TestCase {
                expected_type: token::Token::LBRACE,
                expected_literal: "{",
            },
            TestCase {
                expected_type: token::Token::RBRACE,
                expected_literal: "}",
            },
            TestCase {
                expected_type: token::Token::COMMA,
                expected_literal: ",",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::EOF,
                expected_literal: "EOF",
            },
        ];

        let mut l = Lexer::new(&input);
        for test_case in test_cases {
            let tok = l.next_token();
            assert_eq!(tok, test_case.expected_type);
            assert_eq!(tok.value(), test_case.expected_literal);
        }
    }

    #[test]
    fn test_next_token_identifier() {
        let input = String::from("let five = fn(x);");
        let mut l = Lexer::new(&input);

        struct TestCase<'a> {
            expected_type: token::Token,
            expected_literal: &'a str,
        }

        let test_cases = vec![
            TestCase {
                expected_type: token::Token::LET,
                expected_literal: "let",
            },
            TestCase {
                expected_type: token::Token::IDENT("five".to_string()),
                expected_literal: "five",
            },
            TestCase {
                expected_type: token::Token::ASSIGN,
                expected_literal: "=",
            },
            TestCase {
                expected_type: token::Token::FUNCTION,
                expected_literal: "fn",
            },
            TestCase {
                expected_type: token::Token::LPAREN,
                expected_literal: "(",
            },
            TestCase {
                expected_type: token::Token::IDENT("x".to_string()),
                expected_literal: "x",
            },
            TestCase {
                expected_type: token::Token::RPAREN,
                expected_literal: ")",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::EOF,
                expected_literal: "EOF",
            },
        ];

        for test_case in test_cases {
            let tok = l.next_token();
            assert_eq!(tok, test_case.expected_type);
            assert_eq!(tok.value(), test_case.expected_literal);
        }
    }

    #[test]
    fn test_next_token_int() {
        let input = String::from("let five = 5;");
        let mut l = Lexer::new(&input);

        struct TestCase<'a> {
            expected_type: token::Token,
            expected_literal: &'a str,
        }

        let test_cases = vec![
            TestCase {
                expected_type: token::Token::LET,
                expected_literal: "let",
            },
            TestCase {
                expected_type: token::Token::IDENT("five".to_string()),
                expected_literal: "five",
            },
            TestCase {
                expected_type: token::Token::ASSIGN,
                expected_literal: "=",
            },
            TestCase {
                expected_type: token::Token::INT("5".to_string()),
                expected_literal: "5",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::EOF,
                expected_literal: "EOF",
            },
        ];

        for test_case in test_cases {
            let tok = l.next_token();
            assert_eq!(tok, test_case.expected_type);
            assert_eq!(tok.value(), test_case.expected_literal);
        }
    }

    #[test]
    fn test_next_token_multi_line() {
        let input = String::from(
            "let five = 5;
let ten = 10;
let add = fn(x, y) {
    x + y;
};
let result = add(five, ten);
\"foobar\"
\"foo bar\"
[1, 2];
",
        );
        let mut l = Lexer::new(&input);

        struct TestCase<'a> {
            expected_type: token::Token,
            expected_literal: &'a str,
        }

        let test_cases = vec![
            TestCase {
                expected_type: token::Token::LET,
                expected_literal: "let",
            },
            TestCase {
                expected_type: token::Token::IDENT("five".to_string()),
                expected_literal: "five",
            },
            TestCase {
                expected_type: token::Token::ASSIGN,
                expected_literal: "=",
            },
            TestCase {
                expected_type: token::Token::INT("5".to_string()),
                expected_literal: "5",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::LET,
                expected_literal: "let",
            },
            TestCase {
                expected_type: token::Token::IDENT("ten".to_string()),
                expected_literal: "ten",
            },
            TestCase {
                expected_type: token::Token::ASSIGN,
                expected_literal: "=",
            },
            TestCase {
                expected_type: token::Token::INT("10".to_string()),
                expected_literal: "10",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::LET,
                expected_literal: "let",
            },
            TestCase {
                expected_type: token::Token::IDENT("add".to_string()),
                expected_literal: "add",
            },
            TestCase {
                expected_type: token::Token::ASSIGN,
                expected_literal: "=",
            },
            TestCase {
                expected_type: token::Token::FUNCTION,
                expected_literal: "fn",
            },
            TestCase {
                expected_type: token::Token::LPAREN,
                expected_literal: "(",
            },
            TestCase {
                expected_type: token::Token::IDENT("x".to_string()),
                expected_literal: "x",
            },
            TestCase {
                expected_type: token::Token::COMMA,
                expected_literal: ",",
            },
            TestCase {
                expected_type: token::Token::IDENT("y".to_string()),
                expected_literal: "y",
            },
            TestCase {
                expected_type: token::Token::RPAREN,
                expected_literal: ")",
            },
            TestCase {
                expected_type: token::Token::LBRACE,
                expected_literal: "{",
            },
            TestCase {
                expected_type: token::Token::IDENT("x".to_string()),
                expected_literal: "x",
            },
            TestCase {
                expected_type: token::Token::PLUS,
                expected_literal: "+",
            },
            TestCase {
                expected_type: token::Token::IDENT("y".to_string()),
                expected_literal: "y",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::RBRACE,
                expected_literal: "}",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::LET,
                expected_literal: "let",
            },
            TestCase {
                expected_type: token::Token::IDENT("result".to_string()),
                expected_literal: "result",
            },
            TestCase {
                expected_type: token::Token::ASSIGN,
                expected_literal: "=",
            },
            TestCase {
                expected_type: token::Token::IDENT("add".to_string()),
                expected_literal: "add",
            },
            TestCase {
                expected_type: token::Token::LPAREN,
                expected_literal: "(",
            },
            TestCase {
                expected_type: token::Token::IDENT("five".to_string()),
                expected_literal: "five",
            },
            TestCase {
                expected_type: token::Token::COMMA,
                expected_literal: ",",
            },
            TestCase {
                expected_type: token::Token::IDENT("ten".to_string()),
                expected_literal: "ten",
            },
            TestCase {
                expected_type: token::Token::RPAREN,
                expected_literal: ")",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::STRING("foobar".to_string()),
                expected_literal: "foobar",
            },
            TestCase {
                expected_type: token::Token::STRING("foo bar".to_string()),
                expected_literal: "foo bar",
            },
            TestCase {
                expected_type: token::Token::LBRACKET,
                expected_literal: "[",
            },
            TestCase {
                expected_type: token::Token::INT("1".to_string()),
                expected_literal: "1",
            },
            TestCase {
                expected_type: token::Token::COMMA,
                expected_literal: ",",
            },
            TestCase {
                expected_type: token::Token::INT("2".to_string()),
                expected_literal: "2",
            },
            TestCase {
                expected_type: token::Token::RBRACKET,
                expected_literal: "]",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::EOF,
                expected_literal: "EOF",
            },
        ];

        for test_case in test_cases {
            let tok = l.next_token();
            assert_eq!(tok, test_case.expected_type);
            assert_eq!(tok.value(), test_case.expected_literal);
        }
    }

    #[test]
    fn test_next_token_whitespace() {
        let input = String::from("let \n \t five = 5;");
        let mut l = Lexer::new(&input);

        struct TestCase<'a> {
            expected_type: token::Token,
            expected_literal: &'a str,
        }

        let test_cases = vec![
            TestCase {
                expected_type: token::Token::LET,
                expected_literal: "let",
            },
            TestCase {
                expected_type: token::Token::IDENT("five".to_string()),
                expected_literal: "five",
            },
            TestCase {
                expected_type: token::Token::ASSIGN,
                expected_literal: "=",
            },
            TestCase {
                expected_type: token::Token::INT("5".to_string()),
                expected_literal: "5",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::EOF,
                expected_literal: "EOF",
            },
        ];

        for test_case in test_cases {
            let tok = l.next_token();
            assert_eq!(tok, test_case.expected_type);
            assert_eq!(tok.value(), test_case.expected_literal);
        }
    }

    #[test]
    fn test_next_token_additional_chars() {
        let input = String::from(
            "!-/*5;
                                 5 < 10 > 5;",
        );
        let mut l = Lexer::new(&input);

        struct TestCase<'a> {
            expected_type: token::Token,
            expected_literal: &'a str,
        }

        let test_cases = vec![
            TestCase {
                expected_type: token::Token::BANG,
                expected_literal: "!",
            },
            TestCase {
                expected_type: token::Token::MINUS,
                expected_literal: "-",
            },
            TestCase {
                expected_type: token::Token::SLASH,
                expected_literal: "/",
            },
            TestCase {
                expected_type: token::Token::ASTERISK,
                expected_literal: "*",
            },
            TestCase {
                expected_type: token::Token::INT("5".to_string()),
                expected_literal: "5",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::INT("5".to_string()),
                expected_literal: "5",
            },
            TestCase {
                expected_type: token::Token::LT,
                expected_literal: "<",
            },
            TestCase {
                expected_type: token::Token::INT("10".to_string()),
                expected_literal: "10",
            },
            TestCase {
                expected_type: token::Token::GT,
                expected_literal: ">",
            },
            TestCase {
                expected_type: token::Token::INT("5".to_string()),
                expected_literal: "5",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::EOF,
                expected_literal: "EOF",
            },
        ];

        for test_case in test_cases {
            let tok = l.next_token();
            assert_eq!(tok, test_case.expected_type);
            assert_eq!(tok.value(), test_case.expected_literal);
        }
    }

    #[test]
    fn test_next_token_conditionals() {
        let input = String::from(
            "if (5 < 10) {
                return true;
            } else {
                return false;
            }",
        );

        let mut l = Lexer::new(&input);

        struct TestCase<'a> {
            expected_type: token::Token,
            expected_literal: &'a str,
        }

        let test_cases = vec![
            TestCase {
                expected_type: token::Token::IF,
                expected_literal: "if",
            },
            TestCase {
                expected_type: token::Token::LPAREN,
                expected_literal: "(",
            },
            TestCase {
                expected_type: token::Token::INT("5".to_string()),
                expected_literal: "5",
            },
            TestCase {
                expected_type: token::Token::LT,
                expected_literal: "<",
            },
            TestCase {
                expected_type: token::Token::INT("10".to_string()),
                expected_literal: "10",
            },
            TestCase {
                expected_type: token::Token::RPAREN,
                expected_literal: ")",
            },
            TestCase {
                expected_type: token::Token::LBRACE,
                expected_literal: "{",
            },
            TestCase {
                expected_type: token::Token::RETURN,
                expected_literal: "return",
            },
            TestCase {
                expected_type: token::Token::TRUE,
                expected_literal: "true",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::RBRACE,
                expected_literal: "}",
            },
            TestCase {
                expected_type: token::Token::ELSE,
                expected_literal: "else",
            },
            TestCase {
                expected_type: token::Token::LBRACE,
                expected_literal: "{",
            },
            TestCase {
                expected_type: token::Token::RETURN,
                expected_literal: "return",
            },
            TestCase {
                expected_type: token::Token::FALSE,
                expected_literal: "false",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::RBRACE,
                expected_literal: "}",
            },
            TestCase {
                expected_type: token::Token::EOF,
                expected_literal: "EOF",
            },
        ];

        for test_case in test_cases {
            let tok = l.next_token();
            assert_eq!(tok, test_case.expected_type);
            assert_eq!(tok.value(), test_case.expected_literal);
        }
    }

    #[test]
    fn test_next_token_double_chars() {
        let input = String::from("10 == 10; 10 != 9;");
        let mut l = Lexer::new(&input);

        struct TestCase<'a> {
            expected_type: token::Token,
            expected_literal: &'a str,
        }

        let test_cases = vec![
            TestCase {
                expected_type: token::Token::INT("10".to_string()),
                expected_literal: "10",
            },
            TestCase {
                expected_type: token::Token::EQ,
                expected_literal: "==",
            },
            TestCase {
                expected_type: token::Token::INT("10".to_string()),
                expected_literal: "10",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::INT("10".to_string()),
                expected_literal: "10",
            },
            TestCase {
                expected_type: token::Token::NOTEQ,
                expected_literal: "!=",
            },
            TestCase {
                expected_type: token::Token::INT("9".to_string()),
                expected_literal: "9",
            },
            TestCase {
                expected_type: token::Token::SEMICOLON,
                expected_literal: ";",
            },
            TestCase {
                expected_type: token::Token::EOF,
                expected_literal: "EOF",
            },
        ];

        for test_case in test_cases {
            let tok = l.next_token();
            assert_eq!(tok, test_case.expected_type);
            assert_eq!(tok.value(), test_case.expected_literal);
        }
    }

    #[test]
    fn test_lexer_read_char() {
        let input = String::from("let five = 5;");
        let mut l = Lexer::new(&input);

        let expected = vec![
            'l', 'e', 't', ' ', 'f', 'i', 'v', 'e', ' ', '=', ' ', '5', ';',
        ];

        for ch in expected {
            assert_eq!(l.ch, Some(ch));
            l.read_char();
        }
    }

    #[test]
    fn test_is_letter() {
        let test_cases = vec![
            ('a', true),
            ('z', true),
            ('A', true),
            ('Z', true),
            ('_', true),
            ('0', false),
            ('9', false),
            (' ', false),
            ('+', false),
            ('=', false),
        ];

        for (ch, expected) in test_cases {
            assert_eq!(is_letter(ch), expected, "ch: {}", ch);
        }
    }

    #[test]
    fn test_is_digit() {
        let test_cases = vec![
            ('0', true),
            ('9', true),
            ('a', false),
            ('z', false),
            ('A', false),
            ('Z', false),
            ('_', false),
            (' ', false),
            ('+', false),
            ('=', false),
        ];

        for (ch, expected) in test_cases {
            assert_eq!(is_digit(ch), expected, "ch: {}", ch);
        }
    }

    #[test]
    fn test_lexer_read_identifier() {
        let input = String::from("abcdefg 123");
        let mut l = Lexer::new(&input);

        let identifier = l.read_identifier();
        assert_eq!(identifier, "abcdefg");
    }

    #[test]
    fn test_lexer_read_number() {
        let input = String::from("123 456");
        let mut l = Lexer::new(&input);

        let number = l.read_number();
        assert_eq!(number, "123");
    }

    #[test]
    fn test_lexer_read_string() {
        let input = String::from("\"hello world\"");
        let mut l = Lexer::new(&input);

        let string = l.read_string();
        assert_eq!(string, "hello world");
    }
}
