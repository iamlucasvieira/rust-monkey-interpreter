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
    pub fn new(lexer: &'a mut lexer::Lexer<'a>) -> Parser<'a> {
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

    fn parse_prefix(&mut self, t: &token::Token) -> Result<ast::Expression> {
        info!("Parsing prefix: {:?}", t);
        match t {
            token::Token::IDENT(_) => self.parse_identifier(),
            token::Token::INT(_) => self.parse_integer_literal(),
            token::Token::STRING(_) => self.parse_string_literal(),
            token::Token::BANG | token::Token::MINUS => self.parse_prefix_expression(),
            token::Token::TRUE | token::Token::FALSE => self.parse_boolean(),
            token::Token::LPAREN => self.parse_grouped_expression(),
            token::Token::IF => self.parse_if_expression(),
            token::Token::FUNCTION => self.parse_function_literal(),
            token::Token::LBRACKET => self.parse_array_literal(),
            token::Token::LBRACE => self.parse_hash_literal(),
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
                | token::Token::LPAREN
                | token::Token::LBRACKET
        )
    }

    pub fn parse_program(&mut self) -> Result<ast::Program> {
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

    fn parse_string_literal(&mut self) -> Result<ast::Expression> {
        debug!("Parsing string literal: {:?}", self.cur_token);
        Ok(ast::StringLiteral::new(self.cur_token.clone()).into())
    }

    fn parse_statement(&mut self) -> Result<ast::Statement> {
        info!("Parsing statement: {:?}", self.cur_token);
        match self.cur_token {
            token::Token::LET => self.parse_let_statement(),
            token::Token::RETURN => self.parse_return_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_let_statement(&mut self) -> Result<ast::Statement> {
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

        self.next_token();

        let value = self.parse_expression(Precedence::LOWEST)?;

        if self.peek_token.is_of_type(&token::Token::SEMICOLON) {
            self.next_token();
        }
        Ok(ast::LetStatement::new(let_token, name, value).into())
    }

    fn parse_return_statement(&mut self) -> Result<ast::Statement> {
        let return_token = self.cur_token.clone();

        self.next_token();

        let value = self.parse_expression(Precedence::LOWEST)?;

        if self.peek_token.is_of_type(&token::Token::SEMICOLON) {
            self.next_token();
        }

        Ok(ast::ReturnStatement::new(return_token, value).into())
    }

    fn parse_expression_statement(&mut self) -> Result<ast::Statement> {
        info!("Parsing expression statement");
        let stmt = ast::ExpressionStatement::new(
            self.cur_token.clone(),
            self.parse_expression(Precedence::LOWEST)?,
        );

        if self.peek_token.is_of_type(&token::Token::SEMICOLON) {
            self.next_token();
        }
        Ok(stmt.into())
    }

    fn parse_identifier(&mut self) -> Result<ast::Expression> {
        debug!("Parsing identifier: {:?}", self.cur_token);
        Ok(ast::Identifier::new(self.cur_token.clone()).into())
    }

    fn parse_integer_literal(&mut self) -> Result<ast::Expression> {
        debug!("Parsing integer literal: {:?}", self.cur_token);
        Ok(ast::IntegerLiteral::new(self.cur_token.clone())?.into())
    }

    fn parse_prefix_expression(&mut self) -> Result<ast::Expression> {
        debug!("Parsing prefix expression: {:?}", self.cur_token);
        let operator = self.cur_token.clone();
        self.next_token();
        let right = self.parse_expression(Precedence::PREFIX)?;
        Ok(ast::PrefixExpression::new(operator, right).into())
    }

    fn parse_boolean(&mut self) -> Result<ast::Expression> {
        debug!("Parsing boolean: {:?}", self.cur_token);
        Ok(ast::Boolean::new(self.cur_token.clone()).into())
    }

    fn parse_grouped_expression(&mut self) -> Result<ast::Expression> {
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

    fn parse_if_expression(&mut self) -> Result<ast::Expression> {
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

        Ok(ast::IfExpression::new(if_token, condition, consequence, alternative).into())
    }

    fn parse_function_literal(&mut self) -> Result<ast::Expression> {
        debug!("Parsing function literal: {:?}", self.cur_token);
        let fn_token = self.cur_token.clone();
        if !self.expect_peek(&token::Token::LPAREN) {
            return Err(anyhow!(
                "Expected next token to be '(', got {:?}",
                self.peek_token
            ));
        }

        let parameters = self.parse_function_parameters()?;

        if !self.expect_peek(&token::Token::LBRACE) {
            return Err(anyhow!(
                "Expected next token to be '{{', got {:?}",
                self.peek_token
            ));
        }

        let body = self.parse_block_statement()?;

        Ok(ast::FunctionLiteral::new(fn_token, parameters, body).into())
    }

    fn parse_array_literal(&mut self) -> Result<ast::Expression> {
        debug!("Parsing array literal: {:?}", self.cur_token);
        let array_token = self.cur_token.clone();
        let elements = self.parse_expression_list(&token::Token::RBRACKET)?;
        Ok(ast::ArrayLiteral::new(array_token, elements).into())
    }

    fn parse_hash_literal(&mut self) -> Result<ast::Expression> {
        debug!("Parsing hash literal: {:?}", self.cur_token);
        let hash_token = self.cur_token.clone();
        let mut pairs = Vec::new();

        while !self.peek_token.is_of_type(&token::Token::RBRACE) {
            self.next_token();
            let key = self.parse_expression(Precedence::LOWEST)?;

            if !self.expect_peek(&token::Token::COLON) {
                return Err(anyhow!(
                    "Expected next token to be ':', got {:?}",
                    self.peek_token
                ));
            }

            self.next_token();
            let value = self.parse_expression(Precedence::LOWEST)?;

            pairs.push((key, value));

            if !self.peek_token.is_of_type(&token::Token::RBRACE)
                && !self.expect_peek(&token::Token::COMMA)
            {
                return Err(anyhow!(
                    "Expected next token to be '}}' or ',', got {:?}",
                    self.peek_token
                ));
            }
        }

        if !self.expect_peek(&token::Token::RBRACE) {
            return Err(anyhow!(
                "Expected next token to be '}}', got {:?}",
                self.peek_token
            ));
        }

        Ok(ast::HashLiteral::new(hash_token, pairs).into())
    }

    fn parse_expression_list(&mut self, end: &token::Token) -> Result<Vec<ast::Expression>> {
        let mut list = Vec::new();

        if self.peek_token.is_of_type(end) {
            self.next_token();
            return Ok(list);
        }

        self.next_token();
        list.push(self.parse_expression(Precedence::LOWEST)?);

        while self.peek_token.is_of_type(&token::Token::COMMA) {
            self.next_token();
            self.next_token();
            list.push(self.parse_expression(Precedence::LOWEST)?);
        }

        if !self.expect_peek(end) {
            return Err(anyhow!(
                "Expected next token to be {:?}, got {:?}",
                end,
                self.peek_token
            ));
        }

        Ok(list)
    }

    fn parse_call_expression(&mut self, function: ast::Expression) -> Result<ast::Expression> {
        debug!("Parsing call expression: {:?}", self.cur_token);
        let call_token = self.cur_token.clone();
        let arguments = self.parse_expression_list(&token::Token::RPAREN)?;
        Ok(ast::CallExpression::new(call_token, function, arguments).into())
    }

    fn parse_index_expression(&mut self, left: ast::Expression) -> Result<ast::Expression> {
        debug!("Parsing index expression: {:?}", self.cur_token);
        let index_token = self.cur_token.clone();
        self.next_token();
        let index = self.parse_expression(Precedence::LOWEST)?;

        if !self.expect_peek(&token::Token::RBRACKET) {
            return Err(anyhow!(
                "Expected next token to be ']', got {:?}",
                self.peek_token
            ));
        }

        Ok(ast::IndexExpression::new(index_token, left, index).into())
    }

    fn parse_function_parameters(&mut self) -> Result<Vec<ast::Identifier>> {
        let mut identifiers = Vec::new();

        if self.peek_token.is_of_type(&token::Token::RPAREN) {
            self.next_token();
            return Ok(identifiers);
        }

        self.next_token();

        let ident = ast::Identifier::new(self.cur_token.clone());
        identifiers.push(ident);

        while self.peek_token.is_of_type(&token::Token::COMMA) {
            self.next_token();
            self.next_token();
            let ident = ast::Identifier::new(self.cur_token.clone());
            identifiers.push(ident);
        }

        if !self.expect_peek(&token::Token::RPAREN) {
            return Err(anyhow!(
                "Expected next token to be ')', got {:?}",
                self.peek_token
            ));
        }

        Ok(identifiers)
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

    fn parse_infix(&mut self, left: ast::Expression) -> Result<ast::Expression> {
        debug!("Parsing infix: {:?}", self.cur_token);
        match self.cur_token {
            token::Token::PLUS
            | token::Token::MINUS
            | token::Token::SLASH
            | token::Token::ASTERISK
            | token::Token::EQ
            | token::Token::NOTEQ
            | token::Token::LT
            | token::Token::GT => self.parse_infix_expression(left),
            token::Token::LPAREN => self.parse_call_expression(left),
            token::Token::LBRACKET => self.parse_index_expression(left),
            _ => Err(anyhow!(
                "No infix parse function for {:?}",
                self.cur_token.value()
            )),
        }
    }

    fn parse_infix_expression(&mut self, left: ast::Expression) -> Result<ast::Expression> {
        debug!("Parsing infix expression: {:?}", self.cur_token);
        let operator = self.cur_token.clone();
        let precedence = self.cur_token.precedence();
        self.next_token();
        let right = self.parse_expression(precedence)?;
        Ok(ast::InfixExpression::new(left, operator, right).into())
    }

    fn parse_expression(&mut self, precedence: Precedence) -> Result<ast::Expression> {
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
            left_expression = self.parse_infix(left_expression?);
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
    INDEX,
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::ast::ASTNode;
    use crate::lexer;
    use log::debug;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    fn test_integer_literal(expr: &ast::Expression, value: i64) {
        if let ast::Expression::Integer(int) = expr {
            assert_eq!(int.value, value);
            assert_eq!(int.token_literal(), value.to_string());
        } else {
            panic!("Expected IntegerLiteral, got {:?}", expr);
        }
    }

    fn test_identifier(expr: &ast::Expression, value: &str) {
        if let ast::Expression::Identifier(ident) = expr {
            assert_eq!(ident.value, value);
            assert_eq!(ident.token_literal(), value);
        } else {
            panic!("Expected Identifier, got {:?}", expr);
        }
    }

    fn test_boolean_literal(expr: &ast::Expression, value: bool) {
        if let ast::Expression::Boolean(boolean) = expr {
            assert_eq!(boolean.value, value);
            assert_eq!(boolean.token_literal(), value.to_string());
        } else {
            panic!("Expected Boolean, got {:?}", expr);
        }
    }

    enum Expected<'a> {
        INTEGER(i64),
        IDENTIFIER(&'a str),
        BOOLEAN(bool),
    }

    fn test_literal_expression(expr: &ast::Expression, expected: Expected) {
        match expected {
            Expected::INTEGER(value) => test_integer_literal(expr, value),
            Expected::IDENTIFIER(value) => test_identifier(expr, value),
            Expected::BOOLEAN(value) => test_boolean_literal(expr, value),
        }
    }

    fn test_infix_expression(
        expr: &ast::Expression,
        left: Expected,
        operator: &str,
        right: Expected,
    ) {
        if let ast::Expression::Infix(infix) = expr {
            test_literal_expression(&infix.left, left);
            assert_eq!(infix.operator.value(), operator);
            test_literal_expression(&infix.right, right);
        } else {
            panic!("Expected InfixExpression, got {:?}", expr);
        }
    }

    #[test]
    fn test_let_statments() {
        let test_cases = vec![
            ("let x = 5;", "x", Expected::INTEGER(5)),
            ("let y = true;", "y", Expected::BOOLEAN(true)),
            ("let foobar = y;", "foobar", Expected::IDENTIFIER("y")),
        ];

        for (input, expected_name, expected_value) in test_cases {
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

            if let ast::Statement::Let(stmt) = &program.statements[0] {
                assert_eq!(stmt.name.value, expected_name);
                test_literal_expression(&stmt.value, expected_value);
            } else {
                panic!("Expected LetStatement, got {:?}", program.statements[0]);
            }
        }
    }

    #[test]
    fn test_return_statements() {
        let test_cases = vec![
            ("return 5;", Expected::INTEGER(5)),
            ("return true;", Expected::BOOLEAN(true)),
            ("return foobar;", Expected::IDENTIFIER("foobar")),
        ];

        for (input, expected) in test_cases {
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

            if let ast::Statement::Return(stmt) = &program.statements[0] {
                test_literal_expression(&stmt.return_value, expected);
            } else {
                panic!("Expected ReturnStatement, got {:?}", program.statements[0]);
            }
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

        if let ast::Statement::Expression(stmt) = &program.statements[0] {
            test_identifier(&stmt.expression, "foobar");
        } else {
            panic!(
                "Expected ExpressionStatement, got {:?}",
                program.statements[0]
            );
        }
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

        if let ast::Statement::Expression(stmt) = &program.statements[0] {
            test_integer_literal(&stmt.expression, 5);
        } else {
            panic!(
                "Expected ExpressionStatement, got {:?}",
                program.statements[0]
            );
        }
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

            if let ast::Statement::Expression(stmt) = &program.statements[0] {
                if let ast::Expression::Prefix(prefix) = &stmt.expression {
                    assert_eq!(prefix.operator.value(), operator);
                    test_literal_expression(&prefix.right, expected);
                } else {
                    panic!("Expected PrefixExpression, got {:?}", program.statements[0]);
                }
            } else {
                panic!(
                    "Expected ExpressionStatement, got {:?}",
                    program.statements[0]
                );
            }
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

            if let ast::Statement::Expression(stmt) = &program.statements[0] {
                test_infix_expression(
                    &stmt.expression,
                    expected_left,
                    expected_operator,
                    expected_right,
                );
            } else {
                panic!(
                    "Expected ExpressionStatement, got {:?}",
                    program.statements[0]
                );
            }
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

            if let ast::Statement::Expression(stmt) = &program.statements[0] {
                test_literal_expression(&stmt.expression, Expected::BOOLEAN(expected));
            } else {
                panic!(
                    "Expected ExpressionStatement, got {:?}",
                    program.statements[0]
                );
            }
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
            ("a + add(b * c) + d", "((a + add((b * c))) + d)"),
            (
                "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
                "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))",
            ),
            (
                "add(a + b + c * d / f + g)",
                "add((((a + b) + ((c * d) / f)) + g))",
            ),
            (
                "a * [1, 2, 3, 4][b * c] * d",
                "((a * ([1, 2, 3, 4][(b * c)])) * d)",
            ),
            (
                "add(a * b[2], b[1], 2 * [1, 2][1])",
                "add((a * (b[2])), (b[1]), (2 * ([1, 2][1])))",
            ),
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
                program.to_string(),
                expected,
                "Expected {}, got {}",
                expected,
                program
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

        if let ast::Statement::Expression(stmt) = &program.statements[0] {
            if let ast::Expression::If(expr) = &stmt.expression {
                test_infix_expression(
                    &expr.condition,
                    Expected::IDENTIFIER("x"),
                    "<",
                    Expected::IDENTIFIER("y"),
                );

                let consequence = &expr.consequence.statements[0];
                if let ast::Statement::Expression(stmt) = consequence {
                    test_literal_expression(&stmt.expression, Expected::IDENTIFIER("x"));
                } else {
                    panic!("Expected ExpressionStatement, got {:?}", consequence);
                }
            } else {
                panic!("Expected IfExpression, got {:?}", program.statements[0]);
            }
        } else {
            panic!(
                "Expected ExpressionStatement, got {:?}",
                program.statements[0]
            );
        }
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

        if let ast::Statement::Expression(stmt) = &program.statements[0] {
            if let ast::Expression::If(expr) = &stmt.expression {
                test_infix_expression(
                    &expr.condition,
                    Expected::IDENTIFIER("x"),
                    "<",
                    Expected::IDENTIFIER("y"),
                );

                let consequence = &expr.consequence.statements[0];
                if let ast::Statement::Expression(stmt) = consequence {
                    test_literal_expression(&stmt.expression, Expected::IDENTIFIER("x"));
                } else {
                    panic!("Expected ExpressionStatement, got {:?}", consequence);
                }

                let alternative = &expr.alternative.as_ref().unwrap().statements[0];
                if let ast::Statement::Expression(stmt) = alternative {
                    test_literal_expression(&stmt.expression, Expected::IDENTIFIER("y"));
                } else {
                    panic!("Expected ExpressionStatement, got {:?}", alternative);
                }
            } else {
                panic!("Expected IfExpression, got {:?}", program.statements[0]);
            }
        } else {
            panic!(
                "Expected ExpressionStatement, got {:?}",
                program.statements[0]
            );
        }
    }

    #[test]
    fn test_parse_function_literal() {
        let input = "fn(x, y) { x + y; }";

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

        if let ast::Statement::Expression(stmt) = &program.statements[0] {
            if let ast::Expression::Function(expr) = &stmt.expression {
                assert_eq!(expr.parameters.len(), 2);
                assert_eq!(expr.parameters[0].value, "x");
                assert_eq!(expr.parameters[1].value, "y");

                let body = &expr.body.statements[0];
                if let ast::Statement::Expression(stmt) = body {
                    test_infix_expression(
                        &stmt.expression,
                        Expected::IDENTIFIER("x"),
                        "+",
                        Expected::IDENTIFIER("y"),
                    );
                } else {
                    panic!("Expected ExpressionStatement, got {:?}", body);
                }
            } else {
                panic!("Expected FunctionLiteral, got {:?}", program.statements[0]);
            }
        } else {
            panic!(
                "Expected ExpressionStatement, got {:?}",
                program.statements[0]
            );
        }
    }

    #[test]
    fn test_parse_function_parameters() {
        let test_cases = vec![
            ("fn() {};", vec![]),
            ("fn(x) {};", vec!["x"]),
            ("fn(x, y, z) {};", vec!["x", "y", "z"]),
        ];

        for (input, expected) in test_cases {
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

            if let ast::Statement::Expression(stmt) = &program.statements[0] {
                if let ast::Expression::Function(expr) = &stmt.expression {
                    let params = expr
                        .parameters
                        .iter()
                        .map(|p| p.value.clone())
                        .collect::<Vec<String>>();
                    assert_eq!(params, expected);
                } else {
                    panic!("Expected FunctionLiteral, got {:?}", program.statements[0]);
                }
            } else {
                panic!(
                    "Expected ExpressionStatement, got {:?}",
                    program.statements[0]
                );
            }
        }
    }

    #[test]
    fn test_parse_call_expression() {
        let input = "add(1, 2 * 3, 4 + 5);";

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

        if let ast::Statement::Expression(stmt) = &program.statements[0] {
            if let ast::Expression::Call(call) = &stmt.expression {
                test_identifier(&call.function, "add");
                assert_eq!(call.arguments.len(), 3);

                test_literal_expression(&call.arguments[0], Expected::INTEGER(1));
                test_infix_expression(
                    &call.arguments[1],
                    Expected::INTEGER(2),
                    "*",
                    Expected::INTEGER(3),
                );
                test_infix_expression(
                    &call.arguments[2],
                    Expected::INTEGER(4),
                    "+",
                    Expected::INTEGER(5),
                );
            } else {
                panic!("Expected CallExpression, got {:?}", program.statements[0]);
            }
        } else {
            panic!(
                "Expected ExpressionStatement, got {:?}",
                program.statements[0]
            );
        }
    }

    #[test]
    fn test_string_literal_expression() {
        let input = r#""hello world";"#;

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

        if let ast::Statement::Expression(stmt) = &program.statements[0] {
            if let ast::Expression::String(string) = &stmt.expression {
                assert_eq!(string.value, "hello world");
                assert_eq!(string.token_literal(), "hello world");
            } else {
                panic!("Expected StringLiteral, got {:?}", program.statements[0]);
            }
        } else {
            panic!(
                "Expected ExpressionStatement, got {:?}",
                program.statements[0]
            );
        }
    }

    #[test]
    fn test_parsing_array_literals() {
        let input = "[1, 2 * 2, 3 + 3]";

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

        if let ast::Statement::Expression(stmt) = &program.statements[0] {
            if let ast::Expression::Array(array) = &stmt.expression {
                assert_eq!(array.elements.len(), 3);
                test_integer_literal(&array.elements[0], 1);
                test_infix_expression(
                    &array.elements[1],
                    Expected::INTEGER(2),
                    "*",
                    Expected::INTEGER(2),
                );
                test_infix_expression(
                    &array.elements[2],
                    Expected::INTEGER(3),
                    "+",
                    Expected::INTEGER(3),
                );
            } else {
                panic!("Expected ArrayLiteral, got {:?}", program.statements[0]);
            }
        } else {
            panic!(
                "Expected ExpressionStatement, got {:?}",
                program.statements[0]
            );
        }
    }

    #[test]
    fn test_parsing_index_expressions() {
        let input = "myArray[1 + 1]";

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

        if let ast::Statement::Expression(stmt) = &program.statements[0] {
            if let ast::Expression::Index(index) = &stmt.expression {
                test_identifier(&index.left, "myArray");
                test_infix_expression(
                    &index.index,
                    Expected::INTEGER(1),
                    "+",
                    Expected::INTEGER(1),
                );
            } else {
                panic!("Expected IndexExpression, got {:?}", program.statements[0]);
            }
        } else {
            panic!(
                "Expected ExpressionStatement, got {:?}",
                program.statements[0]
            );
        }
    }

    #[test]
    fn test_parsing_hash_literal_string_keys() {
        let input = r#"{"one": 1, "two": 2, "three": 3}"#;

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

        if let ast::Statement::Expression(stmt) = &program.statements[0] {
            if let ast::Expression::Hash(hash) = &stmt.expression {
                assert_eq!(hash.pairs.len(), 3);

                let mut expected = HashMap::new();
                expected.insert("one", 1);
                expected.insert("two", 2);
                expected.insert("three", 3);

                for (key, value) in &hash.pairs {
                    if let ast::Expression::String(string) = key {
                        test_integer_literal(value, expected[string.value.as_str()]);
                    } else {
                        panic!("Expected StringLiteral, got {:?}", key);
                    }
                }
            } else {
                panic!("Expected HashLiteral, got {:?}", program.statements[0]);
            }
        } else {
            panic!(
                "Expected ExpressionStatement, got {:?}",
                program.statements[0]
            );
        }
    }

    #[test]
    fn test_parsing_hash_literal_empty() {
        let input = "{}";

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

        if let ast::Statement::Expression(stmt) = &program.statements[0] {
            if let ast::Expression::Hash(hash) = &stmt.expression {
                assert_eq!(hash.pairs.len(), 0);
            } else {
                panic!("Expected HashLiteral, got {:?}", program.statements[0]);
            }
        } else {
            panic!(
                "Expected ExpressionStatement, got {:?}",
                program.statements[0]
            );
        }
    }

    #[test]
    fn test_hash_with_expression() {
        let input = r#"{"one": 0 + 1, "two": 10 - 8, "three": 15 / 5}"#;

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

        if let ast::Statement::Expression(stmt) = &program.statements[0] {
            if let ast::Expression::Hash(hash) = &stmt.expression {
                assert_eq!(hash.pairs.len(), 3);

                let mut expected = HashMap::new();
                expected.insert("one", (Expected::INTEGER(0), "+", Expected::INTEGER(1)));
                expected.insert("two", (Expected::INTEGER(10), "-", Expected::INTEGER(8)));
                expected.insert("three", (Expected::INTEGER(15), "/", Expected::INTEGER(5)));

                for (key, value) in &hash.pairs {
                    if let ast::Expression::String(string) = key {
                        if let Some((left, operator, right)) =
                            expected.remove(string.value.as_str())
                        {
                            test_infix_expression(value, left, operator, right);
                        } else {
                            panic!("Expected StringLiteral, got {:?}", key);
                        }
                    } else {
                        panic!("Expected StringLiteral, got {:?}", key);
                    }
                }
            } else {
                panic!("Expected HashLiteral, got {:?}", program.statements[0]);
            }
        } else {
            panic!(
                "Expected ExpressionStatement, got {:?}",
                program.statements[0]
            );
        }
    }
}
