use crate::{ast, lexer, token};
use anyhow::{anyhow, Result};

/// Parser struct
pub struct Parser<'a> {
    lexer: &'a mut lexer::Lexer<'a>,
    cur_token: token::Token,
    peek_token: token::Token,
    pub errors: Vec<String>,
}

/// Parser implementation
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

    fn parse_prefix(&mut self, t: &token::Token) -> Result<Box<dyn ast::Expression>> {
        match t {
            token::Token::IDENT(_) => self.parse_identifier(),
            token::Token::INT(_) => self.parse_integer_literal(),
            token::Token::BANG | token::Token::MINUS => self.parse_prefix_expression(),
            _ => Err(anyhow!("No prefix parse function for {:?}", t.value())),
        }
    }

    fn parse_infix(
        &mut self,
        t: &token::Token,
        left: Box<dyn ast::Expression>,
    ) -> Result<Box<dyn ast::Expression>> {
        if self.has_infix_function(t) {
            return self.parse_infix_expression(left);
        }
        Err(anyhow!("No infix parse function for {:?}", t.value()))
    }

    fn has_infix_function(&self, t: &token::Token) -> bool {
        match t {
            token::Token::PLUS
            | token::Token::MINUS
            | token::Token::SLASH
            | token::Token::ASTERISK
            | token::Token::EQ
            | token::Token::NOTEQ
            | token::Token::LT
            | token::Token::GT => true,
            _ => false,
        }
    }

    fn parse_program(&mut self) -> Result<ast::Program> {
        let mut program = ast::Program::new();

        while self.cur_token != token::Token::EOF {
            let stmt = self.parse_statement();
            match stmt {
                Ok(stmt) => program.statements.push(stmt),
                Err(e) => self.errors.push(e.to_string()),
            }
            self.next_token();
        }

        if self.errors.len() > 0 {
            return Err(anyhow!("Parse errors: \n{:?}", self.errors.join("\n")));
        }
        Ok(program)
    }

    fn parse_statement(&mut self) -> Result<Box<dyn ast::Statement>> {
        match self.cur_token {
            token::Token::LET => self.parse_let_statement(),
            token::Token::RETURN => self.parse_return_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_let_statement(&mut self) -> Result<Box<dyn ast::Statement>> {
        let let_token = self.cur_token.clone();

        if !self.expect_peek(&token::Token::IDENT(String::new())) {
            return Err(anyhow!(
                "Failed to parse let statement: Expected next token to be an identifier, got {:?}",
                self.peek_token.value()
            ));
        }

        let name = self.cur_token.clone();

        if !self.expect_peek(&token::Token::ASSIGN) {
            return Err(anyhow!(
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

    fn parse_return_statement(&mut self) -> Result<Box<dyn ast::Statement>> {
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

    fn parse_expression_statement(&mut self) -> Result<Box<dyn ast::Statement>> {
        let stmt = ast::ExpressionStatement::new(
            self.cur_token.clone(),
            self.parse_expression(Precedence::LOWEST)?,
        );

        if self.peek_token.is_of_type(&token::Token::SEMICOLON) {
            self.next_token();
        }

        return Ok(Box::new(stmt) as Box<dyn ast::Statement>);
    }

    fn parse_identifier(&mut self) -> Result<Box<dyn ast::Expression>> {
        Ok(Box::new(ast::Identifier::new(self.cur_token.clone())))
    }

    fn parse_integer_literal(&mut self) -> Result<Box<dyn ast::Expression>> {
        Ok(Box::new(ast::IntegerLiteral::new(self.cur_token.clone())?))
    }

    fn parse_prefix_expression(&mut self) -> Result<Box<dyn ast::Expression>> {
        let operator = self.cur_token.clone();
        self.next_token();
        let right = self.parse_expression(Precedence::PREFIX)?;
        let prefix = ast::PrefixExpression::new(operator, right);
        Ok(Box::new(prefix))
    }

    fn parse_infix_expression(
        &mut self,
        left: Box<dyn ast::Expression>,
    ) -> Result<Box<dyn ast::Expression>> {
        let operator = self.cur_token.clone();
        let precedence = self.cur_token.precedence();
        self.next_token();
        let right = self.parse_expression(precedence)?;
        let infix = ast::InfixExpression::new(left, operator, right);
        Ok(Box::new(infix))
    }

    fn parse_expression(&mut self, precedence: Precedence) -> Result<Box<dyn ast::Expression>> {
        let mut cur_token = self.cur_token.clone();
        let mut left_expression = self.parse_prefix(&cur_token);
        let mut peek_precedence = self.peek_token.precedence();

        println!("Parsing expression: {:?}", cur_token);
        while !self.peek_token.is_of_type(&token::Token::SEMICOLON) && precedence < peek_precedence
        {
            self.next_token();
            peek_precedence = self.peek_token.precedence();
            cur_token = self.cur_token.clone();

            if self.has_infix_function(&cur_token) {
                left_expression = self.parse_infix(&cur_token, left_expression?);
            } else {
                return left_expression;
            }
        }

        println!("Returning expression:");
        return left_expression;
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

#[derive(PartialOrd, Ord, PartialEq, Eq, Debug)]
pub enum Precedence {
    LOWEST,
    EQUALS,
    LESSGREATER,
    SUM,
    PRODUCT,
    PREFIX,
    CALL,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Node;
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
        let program = match p.parse_program() {
            Ok(program) => program,
            Err(e) => panic!("{}", e),
        };

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
        let program = match p.parse_program() {
            Ok(program) => program,
            Err(e) => panic!("{}", e),
        };

        for stmt in program.statements {
            let stmt = stmt
                .as_any()
                .downcast_ref::<ast::ReturnStatement>()
                .unwrap();
            assert_eq!(ast::Node::token_literal(stmt), "return");
        }
    }

    #[test]
    fn test_parse_identifier_expression() {
        let input = "foobar;";

        let mut l = lexer::Lexer::new(input);
        let mut p = Parser::new(&mut l);
        let program = match p.parse_program() {
            Ok(program) => program,
            Err(e) => panic!("{}", e),
        };

        assert_eq!(p.errors.len(), 0, "Parser has errors");
        assert_eq!(
            program.statements.len(),
            1,
            "Program has wrong number of statements"
        );

        let stmt = program.statements[0]
            .as_any()
            .downcast_ref::<ast::ExpressionStatement>()
            .unwrap();

        let ident = stmt
            .expression
            .as_any()
            .downcast_ref::<ast::Identifier>()
            .unwrap();

        assert_eq!(ident.value, "foobar");
    }

    #[test]
    fn test_parse_integer_expression() {
        let input = "5;";

        let mut l = lexer::Lexer::new(input);
        let mut p = Parser::new(&mut l);
        let program = match p.parse_program() {
            Ok(program) => program,
            Err(e) => panic!("{}", e),
        };

        assert_eq!(p.errors.len(), 0, "Parser has errors");
        assert_eq!(
            program.statements.len(),
            1,
            "Program has wrong number of statements"
        );

        let stmt = program.statements[0]
            .as_any()
            .downcast_ref::<ast::ExpressionStatement>()
            .unwrap();

        let int = stmt
            .expression
            .as_any()
            .downcast_ref::<ast::IntegerLiteral>()
            .unwrap();

        assert_eq!(int.value, 5);
    }

    #[test]
    fn test_parse_prefix_expression() {
        let prefix_tests = vec![("!5;", "!", 5), ("-15;", "-", 15)];

        for (input, operator, value) in prefix_tests {
            let mut l = lexer::Lexer::new(input);
            let mut p = Parser::new(&mut l);
            let program = match p.parse_program() {
                Ok(program) => program,
                Err(e) => panic!("{}", e),
            };

            assert_eq!(p.errors.len(), 0, "Parser has errors");
            assert_eq!(
                program.statements.len(),
                1,
                "Program has wrong number of statements"
            );

            let stmt = program.statements[0]
                .as_any()
                .downcast_ref::<ast::ExpressionStatement>()
                .unwrap();

            let prefix = stmt
                .expression
                .as_any()
                .downcast_ref::<ast::PrefixExpression>()
                .unwrap();

            assert_eq!(prefix.operator.value(), operator);

            let int = prefix
                .right
                .as_any()
                .downcast_ref::<ast::IntegerLiteral>()
                .unwrap();

            assert_eq!(int.value, value);
        }
    }

    #[test]
    fn test_parse_infix_expression() {
        let infix_tests = vec![
            ("5 + 5;", 5, "+", 5),
            ("5 - 5;", 5, "-", 5),
            ("5 * 5;", 5, "*", 5),
            ("5 / 5;", 5, "/", 5),
            ("5 > 5;", 5, ">", 5),
            ("5 < 5;", 5, "<", 5),
            ("5 == 5;", 5, "==", 5),
            ("5 != 5;", 5, "!=", 5),
        ];

        for (input, expected_left, expected_operator, expected_right) in infix_tests {
            let mut l = lexer::Lexer::new(input);
            let mut p = Parser::new(&mut l);

            let program = match p.parse_program() {
                Ok(program) => program,
                Err(e) => panic!("{}", e),
            };

            assert_eq!(p.errors.len(), 0, "Parser has errors");
            assert_eq!(
                program.statements.len(),
                1,
                "Program has wrong number of statements"
            );

            let stmt = program.statements[0]
                .as_any()
                .downcast_ref::<ast::ExpressionStatement>()
                .unwrap();

            let infix = stmt
                .expression
                .as_any()
                .downcast_ref::<ast::InfixExpression>()
                .unwrap();

            let left = infix
                .left
                .as_any()
                .downcast_ref::<ast::IntegerLiteral>()
                .unwrap();

            assert_eq!(left.value, expected_left);

            assert_eq!(infix.operator.value(), expected_operator);

            let right = infix
                .right
                .as_any()
                .downcast_ref::<ast::IntegerLiteral>()
                .unwrap();

            assert_eq!(right.value, expected_right);
        }
    }

    #[test]
    fn test_operator_precedence_parsing() {
        let tests = vec![
            ("-a * b", "((-a) * b)"),
            ("!-a", "(!(-a))"),
            // ("a + b + c", "((a + b) + c)"),
            // ("a + b - c", "((a + b) - c)"),
            // ("a * b * c", "((a * b) * c)"),
            // ("a * b / c", "((a * b) / c)"),
            // ("a + b / c", "(a + (b / c))"),
            // ("a + b * c + d / e - f", "(((a + (b * c)) + (d / e)) - f)"),
            // ("3 + 4; -5 * 5", "(3 + 4)((-5) * 5)"),
            ("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))"),
            ("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4))"),
            // (
            //     "3 + 4 * 5 == 3 * 1 + 4 * 5",
            //     "((3 + (4 * 5)) == ((3 * 1) + (4 * 5))",
            // ),
        ];

        for (input, expected) in tests {
            println!("Testing {}", input);
            let mut l = lexer::Lexer::new(input);
            let mut p = Parser::new(&mut l);
            let program = match p.parse_program() {
                Ok(program) => program,
                Err(e) => panic!("{}", e),
            };

            assert_eq!(p.errors.len(), 0, "Parser has errors");
            assert_eq!(
                program.string(),
                expected,
                "Expected {}, got {}",
                expected,
                program.string()
            );
        }
    }
}
