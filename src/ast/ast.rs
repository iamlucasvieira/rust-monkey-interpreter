use crate::token;

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

pub trait Expression: Node {
    fn expression_node(&self);
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

impl Node for Program {
    fn token_literal(&self) -> &str {
        if self.statements.len() > 0 {
            return self.statements[0].token_literal();
        }
        return "";
    }

    fn string(&self) -> String {
        let mut out = String::new();
        for statement in &self.statements {
            out.push_str(&statement.string());
        }
        return out;
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
        return &self.token.value();
    }

    fn string(&self) -> String {
        let mut out = String::new();
        out.push_str(self.token_literal());
        out.push_str(" ");
        out.push_str(self.name.token_literal());
        out.push_str(" = ");
        out.push_str(self.value.token_literal());
        out.push_str(";");
        return out;
    }
}

impl Statement for LetStatement {
    fn statement_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        return self;
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

impl<'a> Node for Identifier {
    fn token_literal(&self) -> &str {
        return &self.value;
    }

    fn string(&self) -> String {
        return self.value.clone();
    }
}

impl<'a> Expression for Identifier {
    fn expression_node(&self) {}
}

pub struct ReturnStatement {
    pub token: token::Token,
    pub return_value: Box<dyn Expression>,
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
        return &self.token.value();
    }

    fn string(&self) -> String {
        let mut out = String::new();
        out.push_str(self.token_literal());
        out.push_str(" ");
        out.push_str(self.return_value.token_literal());
        out.push_str(";");
        return out;
    }
}

impl Statement for ReturnStatement {
    fn statement_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        return self;
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
        return &self.token.value();
    }

    fn string(&self) -> String {
        return self.expression.string();
    }
}

impl Statement for ExpressionStatement {
    fn statement_node(&self) {}
    fn as_any(&self) -> &dyn Any {
        return self;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::token::token;

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
