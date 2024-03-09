#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    ILLEGAL,
    EOF,

    IDENT(String),
    INT(String),

    ASSIGN,
    PLUS,
    MINUS,
    BANG,
    ASTERISK,
    SLASH,

    LT,
    GT,
    EQ,
    NOTEQ,

    COMMA,
    SEMICOLON,

    LPAREN,
    RPAREN,
    LBRACE,
    RBRACE,

    FUNCTION,
    LET,
    TRUE,
    FALSE,
    IF,
    ELSE,
    RETURN,
}

impl Token {
    pub fn value(&self) -> &str {
        match self {
            Token::ILLEGAL => "ILLEGAL",
            Token::EOF => "EOF",

            Token::IDENT(value) => &value,
            Token::INT(value) => &value,

            Token::ASSIGN => "=",
            Token::PLUS => "+",
            Token::MINUS => "-",
            Token::BANG => "!",
            Token::ASTERISK => "*",
            Token::SLASH => "/",

            Token::LT => "<",
            Token::GT => ">",
            Token::EQ => "==",
            Token::NOTEQ => "!=",

            Token::COMMA => ",",
            Token::SEMICOLON => ";",

            Token::LPAREN => "(",
            Token::RPAREN => ")",
            Token::LBRACE => "{",
            Token::RBRACE => "}",

            Token::FUNCTION => "fn",
            Token::LET => "let",
            Token::TRUE => "true",
            Token::FALSE => "false",
            Token::IF => "if",
            Token::ELSE => "else",
            Token::RETURN => "return",
        }
    }

    pub fn from_literal(literal: &str) -> Token {
        match literal {
            "=" => Token::ASSIGN,
            "+" => Token::PLUS,
            "-" => Token::MINUS,
            "!" => Token::BANG,
            "*" => Token::ASTERISK,
            "/" => Token::SLASH,
            "<" => Token::LT,
            ">" => Token::GT,
            "," => Token::COMMA,
            ";" => Token::SEMICOLON,
            "(" => Token::LPAREN,
            ")" => Token::RPAREN,
            "{" => Token::LBRACE,
            "}" => Token::RBRACE,
            "==" => Token::EQ,
            "!=" => Token::NOTEQ,
            "" => Token::EOF,
            _ => Token::ILLEGAL,
        }
    }

    pub fn from_keyword(keyword: &str) -> Token {
        match keyword {
            "fn" => Token::FUNCTION,
            "let" => Token::LET,
            "true" => Token::TRUE,
            "false" => Token::FALSE,
            "if" => Token::IF,
            "else" => Token::ELSE,
            "return" => Token::RETURN,
            _ => Token::IDENT(keyword.to_string()),
        }
    }

    pub fn is_of_type(&self, t: &Token) -> bool {
        std::mem::discriminant(self) == std::mem::discriminant(t)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_token_value() {
        let tests = vec![
            (Token::ILLEGAL, "ILLEGAL"),
            (Token::EOF, "EOF"),
            (Token::IDENT("foobar".to_string()), "foobar"),
            (Token::INT("123".to_string()), "123"),
            (Token::ASSIGN, "="),
            (Token::PLUS, "+"),
            (Token::MINUS, "-"),
            (Token::BANG, "!"),
            (Token::ASTERISK, "*"),
            (Token::SLASH, "/"),
            (Token::LT, "<"),
            (Token::GT, ">"),
            (Token::EQ, "=="),
            (Token::NOTEQ, "!="),
            (Token::COMMA, ","),
            (Token::SEMICOLON, ";"),
            (Token::LPAREN, "("),
            (Token::RPAREN, ")"),
            (Token::LBRACE, "{"),
            (Token::RBRACE, "}"),
            (Token::FUNCTION, "fn"),
            (Token::LET, "let"),
            (Token::TRUE, "true"),
            (Token::FALSE, "false"),
            (Token::IF, "if"),
            (Token::ELSE, "else"),
            (Token::RETURN, "return"),
        ];

        for (token, expected) in tests {
            assert_eq!(token.value(), expected);
        }
    }

    #[test]
    fn test_token_from_literal() {
        let tests = vec![
            ("=", Token::ASSIGN),
            ("+", Token::PLUS),
            ("-", Token::MINUS),
            ("!", Token::BANG),
            ("*", Token::ASTERISK),
            ("/", Token::SLASH),
            ("<", Token::LT),
            (">", Token::GT),
            (",", Token::COMMA),
            (";", Token::SEMICOLON),
            ("(", Token::LPAREN),
            (")", Token::RPAREN),
            ("{", Token::LBRACE),
            ("}", Token::RBRACE),
            ("==", Token::EQ),
            ("!=", Token::NOTEQ),
            ("", Token::EOF),
            ("foobar", Token::ILLEGAL),
        ];

        for (literal, expected) in tests {
            assert_eq!(Token::from_literal(literal), expected);
        }
    }

    #[test]
    fn test_token_is_of_type() {
        let tests = vec![
            (Token::ILLEGAL, Token::ILLEGAL, true),
            (Token::ILLEGAL, Token::EOF, false),
            (Token::EOF, Token::EOF, true),
            (Token::EOF, Token::ILLEGAL, false),
            (
                Token::IDENT("foobar".to_string()),
                Token::IDENT("foobar".to_string()),
                true,
            ),
            (
                Token::IDENT("foobar".to_string()),
                Token::IDENT("barfoo".to_string()),
                true,
            ),
            (
                Token::INT("123".to_string()),
                Token::INT("123".to_string()),
                true,
            ),
            (
                Token::INT("123".to_string()),
                Token::INT("321".to_string()),
                true,
            ),
            (Token::ASSIGN, Token::ASSIGN, true),
            (Token::ASSIGN, Token::PLUS, false),
            (Token::PLUS, Token::PLUS, true),
            (Token::PLUS, Token::MINUS, false),
            (Token::MINUS, Token::MINUS, true),
            (Token::MINUS, Token::BANG, false),
        ];

        for (token, t, expected) in tests {
            assert_eq!(token.is_of_type(&t), expected);
        }
    }
}
