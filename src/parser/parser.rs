use crate::{ast, lexer, token};

pub struct Parser<'a> {
    lexer: &'a mut lexer::Lexer<'a>,
    cur_token: token::Token,
    peek_token: token::Token,
    pub errors: Vec<String>,
}

impl<'a> Parser<'a> {
    fn new(lexer: &'a mut lexer::Lexer<'a>) -> Parser<'a> {
        let mut p = Parser {
            lexer,
            cur_token: token::Token::EOF,
            peek_token: token::Token::EOF,
            errors: Vec::new(),
        };
        p.next_token();
        p.next_token();
        p
    }

    fn next_token(&mut self) {
        self.cur_token = self.peek_token.clone();
        self.peek_token = self.lexer.next_token();
    }

    fn parse_program(&mut self) -> Result<ast::Program, String> {
        let mut program = ast::Program::new();

        while self.cur_token != token::Token::EOF {
            let stmt = self.parse_statement();
            match stmt {
                Ok(stmt) => program.statements.push(stmt),
                Err(e) => self.errors.push(e),
            }
            self.next_token();
        }

        Ok(program)
    }

    fn parse_statement(&mut self) -> Result<Box<dyn ast::Statement>, String> {
        match self.cur_token {
            token::Token::LET => self.parse_let_statement(),
            token::Token::RETURN => self.parse_return_statement(),
            _ => Err(format!("Unknown token: {:?}", self.cur_token)),
        }
    }

    fn parse_let_statement(&mut self) -> Result<Box<dyn ast::Statement>, String> {
        let let_token = self.cur_token.clone();

        if !self.expect_peek(&token::Token::IDENT(String::new())) {
            return Err(format!(
                "Failed to parse let statement: Expected next token to be an identifier, got {:?}",
                self.peek_token.value()
            ));
        }

        let name = self.cur_token.clone();

        if !self.expect_peek(&token::Token::ASSIGN) {
            return Err(format!(
                "Failed to parse let statement: Expected next token to be '=', got {:?}",
                self.peek_token.value()
            ));
        }

        while !self.cur_token.is_of_type(&token::Token::SEMICOLON) {
            self.next_token();
        }

        let stmt = ast::LetStatement::new(
            let_token,
            name,
            Box::new(ast::Identifier::new(self.cur_token.clone())),
        );

        return Ok(Box::new(stmt) as Box<dyn ast::Statement>);
    }

    fn parse_return_statement(&mut self) -> Result<Box<dyn ast::Statement>, String> {
        let return_token = self.cur_token.clone();

        while !self.cur_token.is_of_type(&token::Token::SEMICOLON) {
            self.next_token();
        }

        let stmt = ast::ReturnStatement::new(
            return_token,
            Box::new(ast::Identifier::new(self.cur_token.clone())),
        );

        return Ok(Box::new(stmt) as Box<dyn ast::Statement>);
    }

    fn expect_peek(&mut self, t: &token::Token) -> bool {
        if self.peek_token.is_of_type(t) {
            self.next_token();
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer;

    const INPUT: &str = r#"
let x = 5;
let y = 10;
let foobar = 838383;
"#;

    #[test]
    fn test_let_statements() {
        let mut l = lexer::Lexer::new(INPUT);
        let mut p = Parser::new(&mut l);
        let program = p.parse_program();

        assert_eq!(program.is_ok(), true);
    }

    #[test]
    fn test_let_statement_identifiers() {
        let mut l = lexer::Lexer::new(INPUT);
        let mut p = Parser::new(&mut l);
        let program = p.parse_program().unwrap();

        let expected = vec!["x", "y", "foobar"];

        for (i, stmt) in program.statements.iter().enumerate() {
            let stmt = stmt.as_any().downcast_ref::<ast::LetStatement>().unwrap();
            assert_eq!(stmt.name.value, expected[i]);
        }
    }

    #[test]
    fn test_return_statements() {
        let input = r#"
return 5;
return 10;
return 993322;
"#;

        let mut l = lexer::Lexer::new(input);
        let mut p = Parser::new(&mut l);
        let program = p.parse_program();

        assert_eq!(program.is_ok(), true);

        for stmt in program.unwrap().statements {
            let stmt = stmt
                .as_any()
                .downcast_ref::<ast::ReturnStatement>()
                .unwrap();
            assert_eq!(ast::Node::token_literal(stmt), "return");
        }
    }
}
