use crate::token;
use anyhow::{Context, Result};
use std::any::Any;

/// The trait Node is implemented by all AST nodes.
pub trait Node {
    fn token_literal(&self) -> &str;
    fn string(&self) -> String;
}

pub trait Statement: Node + Any {
    fn statement_node(&self);
    fn as_any(&self) -> &dyn Any;
}

pub trait Expression: Node + Any {
    fn expression_node(&self);
    fn as_any(&self) -> &dyn Any;
}

pub struct Program {
    pub statements: Vec<Box<dyn Statement>>,
}

impl Program {
    pub fn new() -> Program {
        Program {
            statements: Vec::new(),
        }
    }
}

impl Default for Program {
    fn default() -> Self {
        Self::new()
    }
}

impl Node for Program {
    fn token_literal(&self) -> &str {
        if !self.statements.is_empty() {
            return self.statements[0].token_literal();
        }
        ""
    }

    fn string(&self) -> String {
        let mut out = String::new();
        for statement in &self.statements {
            out.push_str(&statement.string());
        }
        out
    }
}

pub struct LetStatement {
    pub token: token::Token,
    pub name: Identifier,
    pub value: Box<dyn Expression>,
}

impl LetStatement {
    pub fn new(
        token: token::Token,
        name: token::Token,
        value: Box<dyn Expression>,
    ) -> LetStatement {
        LetStatement {
            token,
            name: Identifier::new(name),
            value,
        }
    }
}

impl Node for LetStatement {
    fn token_literal(&self) -> &str {
        self.token.value()
    }

    fn string(&self) -> String {
        let mut out = String::new();
        out.push_str(self.token_literal());
        out.push(' ');
        out.push_str(&self.name.string());
        out.push_str(" = ");
        out.push_str(&self.value.string());
        out.push(';');
        out
    }
}

impl Statement for LetStatement {
    fn statement_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct Identifier {
    pub token: token::Token,
    pub value: String,
}

impl Identifier {
    pub fn new(token: token::Token) -> Identifier {
        let value = token.value().to_string();
        Identifier { token, value }
    }
}

impl Node for Identifier {
    fn token_literal(&self) -> &str {
        &self.value
    }

    fn string(&self) -> String {
        self.value.clone()
    }
}

impl Expression for Identifier {
    fn expression_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

#[derive(Debug)]
pub struct IntegerLiteral {
    pub token: token::Token,
    pub value: i64,
}

impl IntegerLiteral {
    pub fn new(token: token::Token) -> Result<IntegerLiteral> {
        let value = token
            .value()
            .parse::<i64>()
            .with_context(|| format!("Failed to parse integer literal: {}", token.value()))?;
        Ok(IntegerLiteral { token, value })
    }
}

impl Node for IntegerLiteral {
    fn token_literal(&self) -> &str {
        self.token.value()
    }

    fn string(&self) -> String {
        self.value.to_string()
    }
}

impl Expression for IntegerLiteral {
    fn expression_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct Boolean {
    pub token: token::Token,
    pub value: bool,
}

impl Boolean {
    pub fn new(token: token::Token) -> Boolean {
        let value = token.is_of_type(&token::Token::TRUE);
        Boolean { token, value }
    }
}

impl Node for Boolean {
    fn token_literal(&self) -> &str {
        self.token.value()
    }

    fn string(&self) -> String {
        self.token.value().to_string()
    }
}

impl Expression for Boolean {
    fn expression_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct PrefixExpression {
    pub operator: token::Token,
    pub right: Box<dyn Expression>,
}

impl PrefixExpression {
    pub fn new(operator: token::Token, right: Box<dyn Expression>) -> PrefixExpression {
        PrefixExpression { operator, right }
    }
}

impl Node for PrefixExpression {
    fn token_literal(&self) -> &str {
        self.operator.value()
    }

    fn string(&self) -> String {
        let mut out = String::new();
        out.push('(');
        out.push_str(self.operator.value());
        out.push_str(&self.right.string());
        out.push(')');
        out
    }
}

impl Expression for PrefixExpression {
    fn expression_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct InfixExpression {
    pub left: Box<dyn Expression>,
    pub operator: token::Token,
    pub right: Box<dyn Expression>,
}

impl InfixExpression {
    pub fn new(
        left: Box<dyn Expression>,
        operator: token::Token,
        right: Box<dyn Expression>,
    ) -> InfixExpression {
        InfixExpression {
            left,
            operator,
            right,
        }
    }
}

impl Node for InfixExpression {
    fn token_literal(&self) -> &str {
        self.operator.value()
    }

    fn string(&self) -> String {
        let mut out = String::new();
        out.push('(');
        out.push_str(&self.left.string());
        out.push(' ');
        out.push_str(self.operator.value());
        out.push(' ');
        out.push_str(&self.right.string());
        out.push(')');
        out
    }
}

impl Expression for InfixExpression {
    fn expression_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct IfExpression {
    pub token: token::Token,
    pub condition: Box<dyn Expression>,
    pub consequence: BlockStatement,
    pub alternative: Option<BlockStatement>,
}

impl IfExpression {
    pub fn new(
        token: token::Token,
        condition: Box<dyn Expression>,
        consequence: BlockStatement,
        alternative: Option<BlockStatement>,
    ) -> IfExpression {
        IfExpression {
            token,
            condition,
            consequence,
            alternative,
        }
    }
}

impl Node for IfExpression {
    fn token_literal(&self) -> &str {
        self.token.value()
    }

    fn string(&self) -> String {
        let mut out = String::new();
        out.push_str("if");
        out.push(' ');
        out.push('(');
        out.push_str(&self.condition.string());
        out.push(')');
        out.push_str(&self.consequence.string());
        if let Some(alternative) = &self.alternative {
            out.push_str("else");
            out.push_str(&alternative.string());
        }
        out
    }
}

impl Expression for IfExpression {
    fn expression_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct BlockStatement {
    pub token: token::Token,
    pub statements: Vec<Box<dyn Statement>>,
}

impl BlockStatement {
    pub fn new(token: token::Token) -> BlockStatement {
        BlockStatement {
            token,
            statements: Vec::new(),
        }
    }
}

impl Node for BlockStatement {
    fn token_literal(&self) -> &str {
        self.token.value()
    }

    fn string(&self) -> String {
        let mut out = String::new();
        for statement in &self.statements {
            out.push_str(&statement.string());
        }
        out
    }
}

impl Statement for BlockStatement {
    fn statement_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct FunctionLiteral {
    pub token: token::Token,
    pub parameters: Vec<Identifier>,
    pub body: BlockStatement,
}

impl FunctionLiteral {
    pub fn new(
        token: token::Token,
        parameters: Vec<Identifier>,
        body: BlockStatement,
    ) -> FunctionLiteral {
        FunctionLiteral {
            token,
            parameters,
            body,
        }
    }
}

impl Node for FunctionLiteral {
    fn token_literal(&self) -> &str {
        self.token.value()
    }

    fn string(&self) -> String {
        let mut out = String::new();
        out.push_str(self.token_literal());
        out.push('(');
        let params_str = self
            .parameters
            .iter()
            .map(|param| param.string())
            .collect::<Vec<String>>()
            .join(", ");
        out.push_str(&params_str);
        out.push_str(") ");
        out.push_str(&self.body.string());
        out
    }
}

impl Expression for FunctionLiteral {
    fn expression_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct ReturnStatement {
    pub token: token::Token,
    pub return_value: Box<dyn Expression>,
}

pub struct CallExpression {
    pub token: token::Token,
    pub function: Box<dyn Expression>,
    pub arguments: Vec<Box<dyn Expression>>,
}

impl CallExpression {
    pub fn new(
        token: token::Token,
        function: Box<dyn Expression>,
        arguments: Vec<Box<dyn Expression>>,
    ) -> CallExpression {
        CallExpression {
            token,
            function,
            arguments,
        }
    }
}

impl Node for CallExpression {
    fn token_literal(&self) -> &str {
        self.token.value()
    }

    fn string(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.function.string());
        out.push('(');
        let args_str = self
            .arguments
            .iter()
            .map(|arg| arg.string())
            .collect::<Vec<String>>()
            .join(", ");
        out.push_str(&args_str);
        out.push(')');
        out
    }
}

impl Expression for CallExpression {
    fn expression_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl ReturnStatement {
    pub fn new(token: token::Token, return_value: Box<dyn Expression>) -> ReturnStatement {
        ReturnStatement {
            token,
            return_value,
        }
    }
}

impl Node for ReturnStatement {
    fn token_literal(&self) -> &str {
        self.token.value()
    }

    fn string(&self) -> String {
        let mut out = String::new();
        out.push_str(self.token_literal());
        out.push(' ');
        out.push_str(&self.return_value.string());
        out.push(';');
        out
    }
}

impl Statement for ReturnStatement {
    fn statement_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

pub struct ExpressionStatement {
    pub token: token::Token,
    pub expression: Box<dyn Expression>,
}

impl ExpressionStatement {
    pub fn new(token: token::Token, expression: Box<dyn Expression>) -> ExpressionStatement {
        ExpressionStatement { token, expression }
    }
}

impl Node for ExpressionStatement {
    fn token_literal(&self) -> &str {
        self.token.value()
    }

    fn string(&self) -> String {
        self.expression.string()
    }
}

impl Statement for ExpressionStatement {
    fn statement_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::token;

    #[test]
    fn test_string() {
        let program = Program {
            statements: vec![Box::new(LetStatement {
                token: token::Token::LET,
                name: Identifier::new(token::Token::IDENT("myVar".to_string())),
                value: Box::new(Identifier::new(token::Token::IDENT(
                    "anotherVar".to_string(),
                ))),
            })],
        };

        assert_eq!(program.string(), "let myVar = anotherVar;");
    }
}
