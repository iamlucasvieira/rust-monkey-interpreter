use crate::token;
use anyhow::{Context, Result};
use std::fmt;
pub enum Node {
    Program(Program),
    Statement(Statement),
    Expression(Expression),
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Node::Program(p) => write!(f, "{:?}", p),
            Node::Statement(s) => write!(f, "{:?}", s),
            Node::Expression(e) => write!(f, "{:?}", e),
        }
    }
}

#[derive(PartialEq, Eq, Clone)]
pub enum Expression {
    Identifier(Identifier),
    Integer(IntegerLiteral),
    String(StringLiteral),
    Boolean(Boolean),
    Prefix(PrefixExpression),
    Infix(InfixExpression),
    If(IfExpression),
    Block(BlockStatement),
    Function(FunctionLiteral),
    Return(ReturnStatement),
    Call(CallExpression),
    Array(ArrayLiteral),
    Index(IndexExpression),
}

impl Expression {
    fn inner(&self) -> &dyn ASTNode {
        match self {
            Expression::Identifier(ident) => ident,
            Expression::Integer(int) => int,
            Expression::String(s) => s,
            Expression::Boolean(b) => b,
            Expression::Prefix(p) => p,
            Expression::Infix(i) => i,
            Expression::If(i) => i,
            Expression::Block(b) => b,
            Expression::Function(func) => func,
            Expression::Return(r) => r,
            Expression::Call(c) => c,
            Expression::Array(a) => a,
            Expression::Index(i) => i,
        }
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.inner())
    }
}

impl fmt::Debug for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.inner())
    }
}

#[derive(PartialEq, Eq, Clone)]
pub enum Statement {
    Let(LetStatement),
    Return(ReturnStatement),
    Expression(ExpressionStatement),
}

impl Statement {
    fn inner(&self) -> &dyn ASTNode {
        match self {
            Statement::Let(stmt) => stmt,
            Statement::Return(stmt) => stmt,
            Statement::Expression(stmt) => stmt,
        }
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.inner())
    }
}

impl fmt::Debug for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.inner())
    }
}

/// The trait Node is implemented by all AST nodes.
pub trait ASTNode: fmt::Display + fmt::Debug {
    fn token_literal(&self) -> &str;
}

// macro that impl astnode it could be self.token or self.operator default to token
macro_rules! impl_astnode_for {
    ($($t:ty),* $(,)?; $field:ident) => {
        $(
            impl ASTNode for $t {
                fn token_literal(&self) -> &str {
                    self.$field.value()
                }
            }
        )*
    };
    ($($t:ty),* $(,)?) => {
        impl_astnode_for!($($t),*; token);
    };
}

macro_rules! impl_from_for_node {
    ($($source:ty => $variant:ident),* $(,)?) => {
        $(
            impl From<$source> for Node {
                fn from(source: $source) -> Node {
                    Node::$variant(source)
                }
            }
        )*
    };
}

impl_from_for_node!(
    Program => Program,
    Statement => Statement,
    Expression => Expression,
);

#[derive(Debug)]
pub struct Program {
    pub statements: Vec<Statement>,
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

impl ASTNode for Program {
    fn token_literal(&self) -> &str {
        if !self.statements.is_empty() {
            return self.statements[0].inner().token_literal();
        }
        ""
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut out = String::new();
        for statement in &self.statements {
            out.push_str(&statement.to_string());
        }
        write!(f, "{}", out)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct LetStatement {
    pub token: token::Token,
    pub name: Identifier,
    pub value: Expression,
}

impl LetStatement {
    pub fn new(token: token::Token, name: token::Token, value: Expression) -> LetStatement {
        LetStatement {
            token,
            name: Identifier::new(name),
            value,
        }
    }
}

impl From<LetStatement> for Statement {
    fn from(stmt: LetStatement) -> Statement {
        Statement::Let(stmt)
    }
}

impl_astnode_for!(LetStatement);

impl fmt::Display for LetStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut out = String::new();
        out.push_str(self.token_literal());
        out.push(' ');
        out.push_str(&self.name.to_string());
        out.push_str(" = ");
        out.push_str(&self.value.to_string());
        out.push(';');
        write!(f, "{}", out)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
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

impl_astnode_for!(Identifier);

impl From<Identifier> for Expression {
    fn from(ident: Identifier) -> Expression {
        Expression::Identifier(ident)
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
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

impl_astnode_for!(IntegerLiteral);

impl From<IntegerLiteral> for Expression {
    fn from(int: IntegerLiteral) -> Expression {
        Expression::Integer(int)
    }
}

impl fmt::Display for IntegerLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct StringLiteral {
    pub token: token::Token,
    pub value: String,
}

impl StringLiteral {
    pub fn new(token: token::Token) -> StringLiteral {
        let value = token.value().to_string();
        StringLiteral { token, value }
    }
}

impl_astnode_for!(StringLiteral);

impl fmt::Display for StringLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "\'{}\'", self.token.value())
    }
}

impl From<StringLiteral> for Expression {
    fn from(s: StringLiteral) -> Expression {
        Expression::String(s)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
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

impl_astnode_for!(Boolean);

impl From<Boolean> for Expression {
    fn from(b: Boolean) -> Expression {
        Expression::Boolean(b)
    }
}

impl fmt::Display for Boolean {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct PrefixExpression {
    pub operator: token::Token,
    pub right: Box<Expression>,
}

impl PrefixExpression {
    pub fn new(operator: token::Token, right: Expression) -> PrefixExpression {
        PrefixExpression {
            operator,
            right: Box::new(right),
        }
    }
}

impl_astnode_for!(PrefixExpression; operator);

impl From<PrefixExpression> for Expression {
    fn from(prefix: PrefixExpression) -> Expression {
        Expression::Prefix(prefix)
    }
}

impl fmt::Display for PrefixExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}{})", self.operator.value(), self.right)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct InfixExpression {
    pub left: Box<Expression>,
    pub operator: token::Token,
    pub right: Box<Expression>,
}

impl InfixExpression {
    pub fn new(left: Expression, operator: token::Token, right: Expression) -> InfixExpression {
        InfixExpression {
            left: Box::new(left),
            operator,
            right: Box::new(right),
        }
    }
}

impl_astnode_for!(InfixExpression; operator);

impl From<InfixExpression> for Expression {
    fn from(infix: InfixExpression) -> Expression {
        Expression::Infix(infix)
    }
}

impl fmt::Display for InfixExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({} {} {})",
            self.left,
            self.operator.value(),
            self.right
        )
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IfExpression {
    pub token: token::Token,
    pub condition: Box<Expression>,
    pub consequence: BlockStatement,
    pub alternative: Option<BlockStatement>,
}

impl IfExpression {
    pub fn new(
        token: token::Token,
        condition: Expression,
        consequence: BlockStatement,
        alternative: Option<BlockStatement>,
    ) -> IfExpression {
        IfExpression {
            token,
            condition: Box::new(condition),
            consequence,
            alternative,
        }
    }
}

impl_astnode_for!(IfExpression);

impl From<IfExpression> for Expression {
    fn from(if_expr: IfExpression) -> Expression {
        Expression::If(if_expr)
    }
}

impl fmt::Display for IfExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut out = String::new();
        out.push_str("if");
        out.push(' ');
        out.push('(');
        out.push_str(&self.condition.to_string());
        out.push(')');
        out.push_str(&self.consequence.to_string());
        if let Some(alternative) = &self.alternative {
            out.push_str("else");
            out.push_str(&alternative.to_string());
        }
        write!(f, "{}", out)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockStatement {
    pub token: token::Token,
    pub statements: Vec<Statement>,
}

impl BlockStatement {
    pub fn new(token: token::Token) -> BlockStatement {
        BlockStatement {
            token,
            statements: Vec::new(),
        }
    }
}

impl_astnode_for!(BlockStatement);

impl From<BlockStatement> for Expression {
    fn from(block: BlockStatement) -> Expression {
        Expression::Block(block)
    }
}

impl fmt::Display for BlockStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut out = String::new();
        for statement in &self.statements {
            out.push_str(statement.to_string().as_str());
        }
        write!(f, "{}", out)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
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

impl_astnode_for!(FunctionLiteral);

impl From<FunctionLiteral> for Expression {
    fn from(func: FunctionLiteral) -> Expression {
        Expression::Function(func)
    }
}

impl fmt::Display for FunctionLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}({}) {}",
            self.token_literal(),
            self.parameters
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.body
        )
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CallExpression {
    pub token: token::Token,
    pub function: Box<Expression>,
    pub arguments: Vec<Expression>,
}

impl CallExpression {
    pub fn new(
        token: token::Token,
        function: Expression,
        arguments: Vec<Expression>,
    ) -> CallExpression {
        CallExpression {
            token,
            function: Box::new(function),
            arguments,
        }
    }
}

impl_astnode_for!(CallExpression);

impl From<CallExpression> for Expression {
    fn from(call: CallExpression) -> Expression {
        Expression::Call(call)
    }
}

impl fmt::Display for CallExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}({})",
            self.function,
            self.arguments
                .iter()
                .map(|arg| arg.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ArrayLiteral {
    pub token: token::Token,
    pub elements: Vec<Expression>,
}

impl ArrayLiteral {
    pub fn new(token: token::Token, elements: Vec<Expression>) -> ArrayLiteral {
        ArrayLiteral { token, elements }
    }
}

impl_astnode_for!(ArrayLiteral);

impl From<ArrayLiteral> for Expression {
    fn from(array: ArrayLiteral) -> Expression {
        Expression::Array(array)
    }
}

impl fmt::Display for ArrayLiteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "[{}]",
            self.elements
                .iter()
                .map(|elem| elem.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IndexExpression {
    pub token: token::Token,
    pub left: Box<Expression>,
    pub index: Box<Expression>,
}

impl IndexExpression {
    pub fn new(token: token::Token, left: Expression, index: Expression) -> IndexExpression {
        IndexExpression {
            token,
            left: Box::new(left),
            index: Box::new(index),
        }
    }
}

impl_astnode_for!(IndexExpression);

impl From<IndexExpression> for Expression {
    fn from(index: IndexExpression) -> Expression {
        Expression::Index(index)
    }
}

impl fmt::Display for IndexExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}[{}])", self.left, self.index)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ReturnStatement {
    pub token: token::Token,
    pub return_value: Box<Expression>,
}

impl ReturnStatement {
    pub fn new(token: token::Token, return_value: Expression) -> ReturnStatement {
        ReturnStatement {
            token,
            return_value: Box::new(return_value),
        }
    }
}

impl_astnode_for!(ReturnStatement);

impl From<ReturnStatement> for Statement {
    fn from(stmt: ReturnStatement) -> Statement {
        Statement::Return(stmt)
    }
}

impl fmt::Display for ReturnStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {};", self.token_literal(), self.return_value)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ExpressionStatement {
    pub token: token::Token,
    pub expression: Expression,
}

impl ExpressionStatement {
    pub fn new(token: token::Token, expression: Expression) -> ExpressionStatement {
        ExpressionStatement { token, expression }
    }
}

impl_astnode_for!(ExpressionStatement);

impl From<ExpressionStatement> for Statement {
    fn from(stmt: ExpressionStatement) -> Statement {
        Statement::Expression(stmt)
    }
}

impl fmt::Display for ExpressionStatement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.expression)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::token;

    #[test]
    fn test_string() {
        let program = Program {
            statements: vec![Statement::Let(LetStatement {
                token: token::Token::LET,
                name: Identifier::new(token::Token::IDENT("myVar".to_string())),
                value: Expression::Identifier(Identifier::new(token::Token::IDENT(
                    "anotherVar".to_string(),
                ))),
            })],
        };

        assert_eq!(program.to_string(), "let myVar = anotherVar;");
    }
}
