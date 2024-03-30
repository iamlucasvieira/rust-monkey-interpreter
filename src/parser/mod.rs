use crate::{ast, lexer, token};
use anyhow::{anyhow, Result};
use log::{debug, error, info, warn};

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
        debug!("Next token: {:?}", self.cur_token);
    }

    fn parse_prefix(&mut self, t: &token::Token) -> Result<Box<dyn ast::Expression>> {
        info!("Parsing prefix: {:?}", t);
        match t {
            token::Token::IDENT(_) => self.parse_identifier(),
            token::Token::INT(_) => self.parse_integer_literal(),
            token::Token::BANG | token::Token::MINUS => self.parse_prefix_expression(),
            token::Token::TRUE | token::Token::FALSE => self.parse_boolean(),
            token::Token::LPAREN => self.parse_grouped_expression(),
            token::Token::IF => self.parse_if_expression(),
            _ => {
                let message = format!("No prefix parse function for {:?}", t.value());
                error!("{}", message);
                Err(anyhow!(message))
            }
        }
    }

    fn has_infix_function(&self, t: &token::Token) -> bool {
        matches!(
            t,
            token::Token::PLUS
                | token::Token::MINUS
                | token::Token::SLASH
                | token::Token::ASTERISK
                | token::Token::EQ
                | token::Token::NOTEQ
                | token::Token::LT
                | token::Token::GT
        )
    }

    fn parse_program(&mut self) -> Result<ast::Program> {
        info!("Parsing program");
        let mut program = ast::Program::new();
        while self.cur_token != token::Token::EOF {
            let stmt = self.parse_statement();
            match stmt {
                Ok(stmt) => program.statements.push(stmt),
                Err(e) => {
                    warn!("Error parsing statement: {:?}", e);
                    self.errors.push(e.to_string())
                }
            }
            self.next_token();
        }

        if !self.errors.is_empty() {
            return Err(anyhow!("Parse errors: \n{:?}", self.errors.join("\n")));
        }
        Ok(program)
    }

    fn parse_statement(&mut self) -> Result<Box<dyn ast::Statement>> {
        info!("Parsing statement: {:?}", self.cur_token);
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

        Ok(Box::new(stmt) as Box<dyn ast::Statement>)
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

        Ok(Box::new(stmt) as Box<dyn ast::Statement>)
    }

    fn parse_expression_statement(&mut self) -> Result<Box<dyn ast::Statement>> {
        info!("Parsing expression statement");
        let stmt = ast::ExpressionStatement::new(
            self.cur_token.clone(),
            self.parse_expression(Precedence::LOWEST)?,
        );

        if self.peek_token.is_of_type(&token::Token::SEMICOLON) {
            self.next_token();
        }

        Ok(Box::new(stmt) as Box<dyn ast::Statement>)
    }

    fn parse_identifier(&mut self) -> Result<Box<dyn ast::Expression>> {
        debug!("Parsing identifier: {:?}", self.cur_token);
        Ok(Box::new(ast::Identifier::new(self.cur_token.clone())))
    }

    fn parse_integer_literal(&mut self) -> Result<Box<dyn ast::Expression>> {
        debug!("Parsing integer literal: {:?}", self.cur_token);
        Ok(Box::new(ast::IntegerLiteral::new(self.cur_token.clone())?))
    }

    fn parse_prefix_expression(&mut self) -> Result<Box<dyn ast::Expression>> {
        debug!("Parsing prefix expression: {:?}", self.cur_token);
        let operator = self.cur_token.clone();
        self.next_token();
        let right = self.parse_expression(Precedence::PREFIX)?;
        let prefix = ast::PrefixExpression::new(operator, right);
        Ok(Box::new(prefix))
    }

    fn parse_boolean(&mut self) -> Result<Box<dyn ast::Expression>> {
        debug!("Parsing boolean: {:?}", self.cur_token);
        Ok(Box::new(ast::Boolean::new(self.cur_token.clone())))
    }

    fn parse_grouped_expression(&mut self) -> Result<Box<dyn ast::Expression>> {
        debug!("Parsing grouped expression: {:?}", self.cur_token);
        self.next_token();
        let expression = self.parse_expression(Precedence::LOWEST)?;
        if !self.expect_peek(&token::Token::RPAREN) {
            return Err(anyhow!(
                "Expected next token to be ')', got {:?}",
                self.peek_token
            ));
        }
        Ok(expression)
    }

    fn parse_if_expression(&mut self) -> Result<Box<dyn ast::Expression>> {
        debug!("Parsing if expression: {:?}", self.cur_token);
        if !self.expect_peek(&token::Token::LPAREN) {
            return Err(anyhow!(
                "Expected next token to be '(', got {:?}",
                self.peek_token
            ));
        }
        let if_token = self.cur_token.clone();

        self.next_token();
        let condition = self.parse_expression(Precedence::LOWEST)?;

        if !self.expect_peek(&token::Token::RPAREN) {
            return Err(anyhow!(
                "Expected next token to be ')', got {:?}",
                self.peek_token
            ));
        }

        if !self.expect_peek(&token::Token::LBRACE) {
            return Err(anyhow!(
                "Expected next token to be '{{', got {:?}",
                self.peek_token
            ));
        }

        let consequence = self.parse_block_statement()?;
        let mut alternative: Option<ast::BlockStatement> = None;

        if self.peek_token.is_of_type(&token::Token::ELSE) {
            self.next_token();

            if !self.expect_peek(&token::Token::LBRACE) {
                return Err(anyhow!(
                    "Expected next token to be '{{', got {:?}",
                    self.peek_token
                ));
            }

            alternative = self.parse_block_statement().ok();
        }

        let if_expr = ast::IfExpression::new(if_token, condition, consequence, alternative);

        Ok(Box::new(if_expr))
    }

    fn parse_block_statement(&mut self) -> Result<ast::BlockStatement> {
        debug!("Parsing block statement: {:?}", self.cur_token);
        let mut block = ast::BlockStatement::new(self.cur_token.clone());
        self.next_token();

        while !self.cur_token.is_of_type(&token::Token::RBRACE)
            && !self.cur_token.is_of_type(&token::Token::EOF)
        {
            let stmt = self.parse_statement()?;
            block.statements.push(stmt);
            self.next_token();
        }

        Ok(block)
    }

    fn parse_infix_expression(
        &mut self,
        left: Box<dyn ast::Expression>,
    ) -> Result<Box<dyn ast::Expression>> {
        debug!("Parsing infix expression: {:?}", self.cur_token);
        let operator = self.cur_token.clone();
        let precedence = self.cur_token.precedence();
        self.next_token();
        let right = self.parse_expression(precedence)?;
        let infix = ast::InfixExpression::new(left, operator, right);
        Ok(Box::new(infix))
    }

    fn parse_expression(&mut self, precedence: Precedence) -> Result<Box<dyn ast::Expression>> {
        let cur_token = self.cur_token.clone();
        let mut left_expression = self.parse_prefix(&cur_token);
        let mut peek_precedence = self.peek_token.precedence();

        info!(
            "Parsing expression: {:?} with precedence {:?}",
            self.cur_token, precedence
        );

        while !self.peek_token.is_of_type(&token::Token::SEMICOLON) && precedence < peek_precedence
        {
            let peek_token = self.peek_token.clone();

            debug!(
                "Parsing infix expression: {:?} with precedence {:?}",
                peek_token, peek_precedence
            );

            if !self.has_infix_function(&peek_token) {
                return left_expression;
            }

            self.next_token();
            left_expression = self.parse_infix_expression(left_expression?);
            peek_precedence = self.peek_token.precedence();
        }

        debug!("Parse expression done: {:?}", self.cur_token);
        left_expression
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
    use log::debug;

    const INPUT: &str = r#"
let x = 5;
let y = 10;
let foobar = 838383;
"#;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    fn test_integer_literal(expr: &Box<dyn ast::Expression>, value: i64) {
        let int = expr.as_any().downcast_ref::<ast::IntegerLiteral>().unwrap();
        assert_eq!(int.value, value);
        assert_eq!(int.token_literal(), value.to_string());
    }

    fn test_identifier(expr: &Box<dyn ast::Expression>, value: &str) {
        let ident = expr.as_any().downcast_ref::<ast::Identifier>().unwrap();
        assert_eq!(ident.value, value);
        assert_eq!(ident.token_literal(), value);
    }

    fn test_boolean_literal(expr: &Box<dyn ast::Expression>, value: bool) {
        let boolean = expr.as_any().downcast_ref::<ast::Boolean>().unwrap();
        assert_eq!(boolean.value, value);
        assert_eq!(boolean.token_literal(), value.to_string());
    }

    enum Expected<'a> {
        INTEGER(i64),
        IDENTIFIER(&'a str),
        BOOLEAN(bool),
    }

    fn test_literal_expression(expr: &Box<dyn ast::Expression>, expected: Expected) {
        match expected {
            Expected::INTEGER(value) => test_integer_literal(expr, value),
            Expected::IDENTIFIER(value) => test_identifier(expr, value),
            Expected::BOOLEAN(value) => test_boolean_literal(expr, value),
        }
    }

    fn test_infix_expression(
        expr: &Box<dyn ast::Expression>,
        left: Expected,
        operator: &str,
        right: Expected,
    ) {
        let infix = expr
            .as_any()
            .downcast_ref::<ast::InfixExpression>()
            .unwrap();
        test_literal_expression(&infix.left, left);
        assert_eq!(infix.operator.value(), operator);
        test_literal_expression(&infix.right, right);
    }

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

        assert!(p.errors.is_empty(), "Parser has errors");
        assert_eq!(
            program.statements.len(),
            1,
            "Program has wrong number of statements"
        );

        let stmt = program.statements[0]
            .as_any()
            .downcast_ref::<ast::ExpressionStatement>()
            .unwrap();

        test_literal_expression(&stmt.expression, Expected::IDENTIFIER("foobar"));
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

        assert!(p.errors.is_empty(), "Parser has errors");
        assert_eq!(
            program.statements.len(),
            1,
            "Program has wrong number of statements"
        );

        let stmt = program.statements[0]
            .as_any()
            .downcast_ref::<ast::ExpressionStatement>()
            .unwrap();

        test_literal_expression(&stmt.expression, Expected::INTEGER(5));
    }

    #[test]
    fn test_parse_prefix_expression() {
        let prefix_tests = vec![
            ("!5;", "!", Expected::INTEGER(5)),
            ("-15;", "-", Expected::INTEGER(15)),
            ("!true;", "!", Expected::BOOLEAN(true)),
            ("!false;", "!", Expected::BOOLEAN(false)),
        ];

        for (input, operator, expected) in prefix_tests {
            let mut l = lexer::Lexer::new(input);
            let mut p = Parser::new(&mut l);
            let program = match p.parse_program() {
                Ok(program) => program,
                Err(e) => panic!("{}", e),
            };

            assert!(p.errors.is_empty(), "Parser has errors");
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

            test_literal_expression(&prefix.right, expected);
        }
    }

    #[test]
    fn test_parse_infix_expression() {
        let infix_tests = vec![
            ("5 + 5;", Expected::INTEGER(5), "+", Expected::INTEGER(5)),
            ("5 - 5;", Expected::INTEGER(5), "-", Expected::INTEGER(5)),
            ("5 * 5;", Expected::INTEGER(5), "*", Expected::INTEGER(5)),
            ("5 / 5;", Expected::INTEGER(5), "/", Expected::INTEGER(5)),
            ("5 > 5;", Expected::INTEGER(5), ">", Expected::INTEGER(5)),
            ("5 < 5;", Expected::INTEGER(5), "<", Expected::INTEGER(5)),
            ("5 == 5;", Expected::INTEGER(5), "==", Expected::INTEGER(5)),
            ("5 != 5;", Expected::INTEGER(5), "!=", Expected::INTEGER(5)),
            (
                "true == true",
                Expected::BOOLEAN(true),
                "==",
                Expected::BOOLEAN(true),
            ),
            (
                "true != false",
                Expected::BOOLEAN(true),
                "!=",
                Expected::BOOLEAN(false),
            ),
            (
                "false == false",
                Expected::BOOLEAN(false),
                "==",
                Expected::BOOLEAN(false),
            ),
        ];

        for (input, expected_left, expected_operator, expected_right) in infix_tests {
            let mut l = lexer::Lexer::new(input);
            let mut p = Parser::new(&mut l);

            let program = match p.parse_program() {
                Ok(program) => program,
                Err(e) => panic!("{}", e),
            };

            assert!(p.errors.is_empty(), "Parser has errors");
            assert_eq!(
                program.statements.len(),
                1,
                "Program has wrong number of statements"
            );

            let stmt = program.statements[0]
                .as_any()
                .downcast_ref::<ast::ExpressionStatement>()
                .unwrap();

            test_infix_expression(
                &stmt.expression,
                expected_left,
                expected_operator,
                expected_right,
            );
        }
    }

    #[test]
    fn test_parse_boolean_expression() {
        let infix_tests = vec![("true;", true), ("false;", false)];

        for (input, expected) in infix_tests {
            let mut l = lexer::Lexer::new(input);
            let mut p = Parser::new(&mut l);

            let program = match p.parse_program() {
                Ok(program) => program,
                Err(e) => panic!("{}", e),
            };

            assert!(p.errors.is_empty(), "Parser has errors");
            assert_eq!(
                program.statements.len(),
                1,
                "Program has wrong number of statements"
            );

            let stmt = program.statements[0]
                .as_any()
                .downcast_ref::<ast::ExpressionStatement>()
                .unwrap();

            test_literal_expression(&stmt.expression, Expected::BOOLEAN(expected));
        }
    }

    #[test]
    fn test_operator_precedence_parsing() {
        let tests = vec![
            ("1 + 2 + 3", "((1 + 2) + 3)"),
            ("-a * b", "((-a) * b)"),
            ("!-a", "(!(-a))"),
            ("a + b + c", "((a + b) + c)"),
            ("a + b - c", "((a + b) - c)"),
            ("a * b * c", "((a * b) * c)"),
            ("a * b / c", "((a * b) / c)"),
            ("a + b / c", "(a + (b / c))"),
            ("a + b * c + d / e - f", "(((a + (b * c)) + (d / e)) - f)"),
            ("3 + 4; -5 * 5", "(3 + 4)((-5) * 5)"),
            ("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))"),
            ("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4))"),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
            ("-1 + 2", "((-1) + 2)"),
            ("3 > 5 ==  false", "((3 > 5) == false)"),
            ("3 < 5 == true", "((3 < 5) == true)"),
            ("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)"),
            ("(5 + 5) * 2", "((5 + 5) * 2)"),
            ("2 / (5 + 5)", "(2 / (5 + 5))"),
            ("-(5 + 5)", "(-(5 + 5))"),
            ("!(true == true)", "(!(true == true))"),
        ];

        for (input, expected) in tests {
            init();
            debug!("Testing {}", input);
            let mut l = lexer::Lexer::new(input);
            let mut p = Parser::new(&mut l);
            let program = match p.parse_program() {
                Ok(program) => program,
                Err(e) => panic!("{}", e),
            };

            assert!(p.errors.is_empty(), "Parser has errors");
            assert_eq!(
                program.string(),
                expected,
                "Expected {}, got {}",
                expected,
                program.string()
            );
        }
    }

    #[test]
    fn test_parse_if_expression() {
        init();
        let input = "if (x < y) { x }";

        let mut l = lexer::Lexer::new(input);
        let mut p = Parser::new(&mut l);
        let program = match p.parse_program() {
            Ok(program) => program,
            Err(e) => panic!("{}", e),
        };

        assert!(p.errors.is_empty(), "Parser has errors");
        assert_eq!(
            program.statements.len(),
            1,
            "Program has wrong number of statements"
        );

        let stmt = program.statements[0]
            .as_any()
            .downcast_ref::<ast::ExpressionStatement>()
            .unwrap();

        let expr = stmt
            .expression
            .as_any()
            .downcast_ref::<ast::IfExpression>()
            .unwrap();

        test_infix_expression(
            &expr.condition,
            Expected::IDENTIFIER("x"),
            "<",
            Expected::IDENTIFIER("y"),
        );

        let consequence = expr.consequence.statements[0]
            .as_any()
            .downcast_ref::<ast::ExpressionStatement>()
            .unwrap();

        test_literal_expression(&consequence.expression, Expected::IDENTIFIER("x"));
    }

    #[test]
    fn test_parse_if_expression_with_else() {
        let input = "if (x < y) { x } else { y }";

        let mut l = lexer::Lexer::new(input);
        let mut p = Parser::new(&mut l);
        let program = match p.parse_program() {
            Ok(program) => program,
            Err(e) => panic!("{}", e),
        };

        assert!(p.errors.is_empty(), "Parser has errors");
        assert_eq!(
            program.statements.len(),
            1,
            "Program has wrong number of statements"
        );

        let stmt = program.statements[0]
            .as_any()
            .downcast_ref::<ast::ExpressionStatement>()
            .unwrap();

        let expr = stmt
            .expression
            .as_any()
            .downcast_ref::<ast::IfExpression>()
            .unwrap();

        test_infix_expression(
            &expr.condition,
            Expected::IDENTIFIER("x"),
            "<",
            Expected::IDENTIFIER("y"),
        );

        let consequence = expr.consequence.statements[0]
            .as_any()
            .downcast_ref::<ast::ExpressionStatement>()
            .unwrap();

        test_literal_expression(&consequence.expression, Expected::IDENTIFIER("x"));

        let alternative = expr.alternative.as_ref().unwrap().statements[0]
            .as_any()
            .downcast_ref::<ast::ExpressionStatement>()
            .unwrap();

        test_literal_expression(&alternative.expression, Expected::IDENTIFIER("y"));
    }
}
