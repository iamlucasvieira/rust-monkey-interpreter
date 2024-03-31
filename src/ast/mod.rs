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

pub enum Expression {
    Identifier(Identifier),
    Integer(IntegerLiteral),
    Boolean(Boolean),
    Prefix(PrefixExpression),
    Infix(InfixExpression),
    If(IfExpression),
    Block(BlockStatement),
    Function(FunctionLiteral),
    Return(ReturnStatement),
    Call(CallExpression),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Identifier(ident) => write!(f, "{}", ident),
            Expression::Integer(int) => write!(f, "{}", int),
            Expression::Boolean(b) => write!(f, "{}", b),
            Expression::Prefix(p) => write!(f, "{}", p),
            Expression::Infix(i) => write!(f, "{}", i),
            Expression::If(i) => write!(f, "{}", i),
            Expression::Block(b) => write!(f, "{}", b),
            Expression::Function(func) => write!(f, "{}", func),
            Expression::Return(r) => write!(f, "{}", r),
            Expression::Call(c) => write!(f, "{}", c),
        }
    }
}

impl fmt::Debug for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Identifier(ident) => write!(f, "{:?}", ident),
            Expression::Integer(int) => write!(f, "{:?}", int),
            Expression::Boolean(b) => write!(f, "{:?}", b),
            Expression::Prefix(p) => write!(f, "{:?}", p),
            Expression::Infix(i) => write!(f, "{:?}", i),
            Expression::If(i) => write!(f, "{:?}", i),
            Expression::Block(b) => write!(f, "{:?}", b),
            Expression::Function(func) => write!(f, "{:?}", func),
            Expression::Return(r) => write!(f, "{:?}", r),
            Expression::Call(c) => write!(f, "{:?}", c),
        }
    }
}

pub enum Statement {
    Let(LetStatement),
    Return(ReturnStatement),
    Expression(ExpressionStatement),
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Statement::Let(stmt) => write!(f, "{}", stmt),
            Statement::Return(stmt) => write!(f, "{}", stmt),
            Statement::Expression(stmt) => write!(f, "{}", stmt),
        }
    }
}

impl fmt::Debug for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Statement::Let(stmt) => write!(f, "{:?}", stmt),
            Statement::Return(stmt) => write!(f, "{:?}", stmt),
            Statement::Expression(stmt) => write!(f, "{:?}", stmt),
        }
    }
}

impl Statement {
    pub fn token_literal(&self) -> &str {
        match self {
            Statement::Let(stmt) => stmt.token_literal(),
            Statement::Return(stmt) => stmt.token_literal(),
            Statement::Expression(stmt) => stmt.token_literal(),
        }
    }
}

/// The trait Node is implemented by all AST nodes.
pub trait ASTNode: fmt::Display {
    fn token_literal(&self) -> &str;
}

impl From<Program> for Node {
    fn from(program: Program) -> Node {
        Node::Program(program)
    }
}

impl From<Statement> for Node {
    fn from(statement: Statement) -> Node {
        Node::Statement(statement)
    }
}

impl From<Expression> for Node {
    fn from(expression: Expression) -> Node {
        Node::Expression(expression)
    }
}

impl fmt::Debug for dyn ASTNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

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
            return self.statements[0].token_literal();
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

#[derive(Debug)]
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

impl ASTNode for LetStatement {
    fn token_literal(&self) -> &str {
        self.token.value()
    }
}

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

#[derive(Debug)]
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

impl ASTNode for Identifier {
    fn token_literal(&self) -> &str {
        &self.value
    }
}

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

impl ASTNode for IntegerLiteral {
    fn token_literal(&self) -> &str {
        self.token.value()
    }
}

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

#[derive(Debug)]
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

impl ASTNode for Boolean {
    fn token_literal(&self) -> &str {
        self.token.value()
    }
}

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

#[derive(Debug)]
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

impl ASTNode for PrefixExpression {
    fn token_literal(&self) -> &str {
        self.operator.value()
    }
}

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

#[derive(Debug)]
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

impl ASTNode for InfixExpression {
    fn token_literal(&self) -> &str {
        self.operator.value()
    }
}

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

#[derive(Debug)]
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

impl ASTNode for IfExpression {
    fn token_literal(&self) -> &str {
        self.token.value()
    }
}

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

#[derive(Debug)]
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

impl ASTNode for BlockStatement {
    fn token_literal(&self) -> &str {
        self.token.value()
    }
}

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

#[derive(Debug)]
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

impl ASTNode for FunctionLiteral {
    fn token_literal(&self) -> &str {
        self.token.value()
    }
}

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

#[derive(Debug)]
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

impl ASTNode for CallExpression {
    fn token_literal(&self) -> &str {
        self.token.value()
    }
}

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

#[derive(Debug)]
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

impl ASTNode for ReturnStatement {
    fn token_literal(&self) -> &str {
        self.token.value()
    }
}

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

#[derive(Debug)]
pub struct ExpressionStatement {
    pub token: token::Token,
    pub expression: Expression,
}

impl ExpressionStatement {
    pub fn new(token: token::Token, expression: Expression) -> ExpressionStatement {
        ExpressionStatement { token, expression }
    }
}

impl ASTNode for ExpressionStatement {
    fn token_literal(&self) -> &str {
        self.token.value()
    }
}

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
