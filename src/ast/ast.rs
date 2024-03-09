use crate::token;

/// The trait Node is implemented by all AST nodes.
pub trait Node {
    fn token_literal(&self) -> &str;
}

pub trait Statement: Node {
    fn statement_node(&self);
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

impl<'a> Node for LetStatement {
    fn token_literal(&self) -> &str {
        return &self.token.value();
    }
}

impl<'a> Statement for LetStatement {
    fn statement_node(&self) {}
}

pub struct Identifier {
    token: token::Token,
    value: String,
}

impl Identifier {
    pub fn new(token: token::Token) -> Identifier {
        Identifier {
            token: token.clone(),
            value: token.value().to_string(),
        }
    }
}

impl<'a> Node for Identifier {
    fn token_literal(&self) -> &str {
        return &self.token.value();
    }
}

impl<'a> Expression for Identifier {
    fn expression_node(&self) {}
}
