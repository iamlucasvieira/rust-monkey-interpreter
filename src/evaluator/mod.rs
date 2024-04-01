use crate::ast;
use crate::object::{self, Object};
use crate::token;
use anyhow::Result;
use log::{debug, error};

pub fn eval(node: ast::Node) -> Result<Object> {
    debug!("eval: {:?}", node);
    match node {
        ast::Node::Program(program) => eval_program(program),
        ast::Node::Statement(stmt) => eval_statement(stmt),
        ast::Node::Expression(expr) => eval_expression(expr),
    }
}

fn eval_program(program: ast::Program) -> Result<Object> {
    let mut result = Object::Null;

    for stmt in program.statements {
        result = eval(stmt.into())?;
        if let Object::Return(value) = result {
            return Ok(*value);
        }
    }
    Ok(result)
}

fn eval_statement(stmt: ast::Statement) -> Result<Object> {
    match stmt {
        ast::Statement::Expression(expr) => eval(ast::Node::Expression(expr.expression)),
        ast::Statement::Return(expr) => eval(ast::Node::Expression(ast::Expression::Return(expr))),
        _ => {
            error!("eval_statement: {:?}", stmt);
            Ok(object::NULL)
        }
    }
}

fn eval_expression(expr: ast::Expression) -> Result<Object> {
    match expr {
        ast::Expression::Integer(literal) => Ok(Object::Integer(literal.value)),
        ast::Expression::Boolean(literal) => eval_boolean(literal),
        ast::Expression::Prefix(literal) => eval_prefix_expression(literal),
        ast::Expression::Infix(literal) => eval_infix_expression(literal),
        ast::Expression::Block(literal) => eval_block_statement(literal),
        ast::Expression::If(literal) => eval_if_expression(literal),
        ast::Expression::Return(literal) => eval_return_expression(literal),
        _ => {
            error!("eval_expression: {:?}", expr);
            Ok(object::NULL)
        }
    }
}

fn eval_block_statement(stmt: ast::BlockStatement) -> Result<Object> {
    let mut result = Object::Null;

    for stmt in stmt.statements {
        result = eval(stmt.into())?;
        if let Object::Return(_) = result {
            return Ok(result);
        }
    }
    Ok(result)
}

fn eval_return_expression(expr: ast::ReturnStatement) -> Result<Object> {
    let value = eval((*expr.return_value).into())?;
    Ok(Object::Return(Box::new(value)))
}

fn eval_if_expression(expr: ast::IfExpression) -> Result<Object> {
    let condition = eval((*expr.condition).into())?;
    if is_truthy(condition) {
        let consequence: ast::Expression = expr.consequence.into();
        eval(consequence.into())
    } else if let Some(alternative) = expr.alternative {
        let alternative: ast::Expression = alternative.into();
        eval(alternative.into())
    } else {
        Ok(object::NULL)
    }
}

fn is_truthy(obj: Object) -> bool {
    match obj {
        object::NULL => false,
        object::TRUE => true,
        object::FALSE => false,
        _ => true,
    }
}

fn eval_boolean(expr: ast::Boolean) -> Result<Object> {
    Ok(object::Object::from_bool(expr.value))
}

fn eval_prefix_expression(expr: ast::PrefixExpression) -> Result<Object> {
    match expr.operator.to_string().as_str() {
        "!" => {
            let right = eval_expression(*expr.right)?;
            eval_bang_operator_expression(right)
        }
        "-" => {
            let right = eval_expression(*expr.right)?;
            eval_minus_prefix_operator_expression(right)
        }
        _ => {
            error!("eval_prefix_expression: {:?}", expr);
            Ok(object::NULL)
        }
    }
}

fn eval_bang_operator_expression(right: Object) -> Result<Object> {
    match right {
        object::TRUE => Ok(object::FALSE),
        object::FALSE => Ok(object::TRUE),
        object::NULL => Ok(object::TRUE),
        _ => Ok(object::FALSE),
    }
}

fn eval_minus_prefix_operator_expression(right: Object) -> Result<Object> {
    match right {
        Object::Integer(value) => Ok(Object::Integer(-value)),
        _ => Ok(object::NULL),
    }
}

fn eval_infix_expression(expr: ast::InfixExpression) -> Result<Object> {
    let left = eval_expression(*expr.left)?;
    let right = eval_expression(*expr.right)?;

    match (&left, &right) {
        (Object::Integer(left), Object::Integer(right)) => {
            eval_integer_infix_expression(left, expr.operator.to_string().as_str(), right)
        }
        (_, _) if expr.operator == token::Token::EQ => Ok(object::Object::from_bool(left == right)),
        (_, _) if expr.operator == token::Token::NOTEQ => {
            Ok(object::Object::from_bool(left != right))
        }

        _ => {
            error!(
                "Invalid infix expression: left={:?}, right={:?}",
                left, right
            );
            Ok(object::NULL)
        }
    }
}

fn eval_integer_infix_expression(left: &i64, operator: &str, right: &i64) -> Result<Object> {
    match operator {
        "+" => Ok(Object::Integer(left + right)),
        "-" => Ok(Object::Integer(left - right)),
        "*" => Ok(Object::Integer(left * right)),
        "/" => Ok(Object::Integer(left / right)),
        "<" => Ok(object::Object::from_bool(left < right)),
        ">" => Ok(object::Object::from_bool(left > right)),
        "==" => Ok(object::Object::from_bool(left == right)),
        "!=" => Ok(object::Object::from_bool(left != right)),
        _ => {
            error!("Invalid operator: {} for integers", operator);
            Ok(object::NULL)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::object::tests::{test_boolean_object, test_integer_object, test_null_object};
    use crate::parser::Parser;
    use log::debug;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    fn test_eval(input: &str) -> Object {
        let mut l = Lexer::new(input);
        let mut p = Parser::new(&mut l);
        let program = p.parse_program().unwrap();
        eval(program.into()).unwrap()
    }

    #[test]
    fn test_eval_integer_expression() {
        init();
        debug!("test_eval_integer_expression");
        let tests = vec![
            ("5", 5),
            ("10", 10),
            ("-10", -10),
            ("-5", -5),
            ("5 + 5 + 5 + 5 - 10", 10),
            ("2 * 2 * 2 * 2 * 2", 32),
            ("-50 + 100 + -50", 0),
            ("5 * 2 + 10", 20),
            ("5 + 2 * 10", 25),
            ("20 + 2 * -10", 0),
            ("50 / 2 * 2 + 10", 60),
            ("2 * (5 + 10)", 30),
            ("3 * 3 * 3 + 10", 37),
            ("3 * (3 * 3) + 10", 37),
            ("(5 + 10 * 2 + 15 / 3) * 2 + -10", 50),
        ];

        for (input, expected) in tests {
            let evaluated = test_eval(input);
            test_integer_object(evaluated, expected);
        }
    }

    #[test]
    fn test_eval_boolean_expression() {
        init();
        debug!("test_eval_boolean_expression");
        let tests = vec![
            ("true", true),
            ("false", false),
            ("1 < 2", true),
            ("1 > 2", false),
            ("1 < 1", false),
            ("1 > 1", false),
            ("1 == 1", true),
            ("1 != 1", false),
            ("1 == 2", false),
            ("1 != 2", true),
            ("true == true", true),
            ("false == false", true),
            ("true == false", false),
            ("true != false", true),
            ("false != true", true),
            ("(1 < 2) == true", true),
            ("(1 < 2) == false", false),
            ("(1 > 2) == true", false),
            ("(1 > 2) == false", true),
        ];

        for (input, expected) in tests {
            let evaluated = test_eval(input);
            test_boolean_object(evaluated, expected);
        }
    }

    #[test]
    fn test_bang_operator() {
        init();
        debug!("test_bang_operator");
        let tests = vec![
            ("!true", false),
            ("!false", true),
            ("!5", false),
            ("!!true", true),
            ("!!false", false),
            ("!!5", true),
        ];

        for (input, expected) in tests {
            let evaluated = test_eval(input);
            test_boolean_object(evaluated, expected);
        }
    }

    #[test]
    fn test_if_else() {
        init();
        debug!("test_id_else");
        let tests = vec![
            ("if (true) { 10 }", Some(10)),
            ("if (false) { 10 }", None),
            ("if (1) { 10 }", Some(10)),
            ("if (1 < 2) { 10 }", Some(10)),
            ("if (1 > 2) { 10 }", None),
            ("if (1 > 2) { 10 } else { 20 }", Some(20)),
            ("if (1 < 2) { 10 } else { 20 }", Some(10)),
        ];

        for (input, expected) in tests {
            let evaluated = test_eval(input);
            match expected {
                Some(value) => test_integer_object(evaluated, value),
                None => test_null_object(evaluated),
            }
        }
    }

    #[test]
    fn test_return_statement() {
        init();
        debug!("test_return_statement");
        let tests = vec![
            ("return 10;", 10),
            ("return 10; 9;", 10),
            ("return 2 * 5; 9;", 10),
            ("9; return 2 * 5; 9;", 10),
            (
                "if (10 > 1) {
                    if (10 > 1) {
                        return 10;
                    }
                    return 1;
                }",
                10,
            ),
        ];

        for (input, expected) in tests {
            let evaluated = test_eval(input);
            test_integer_object(evaluated, expected);
        }
    }
}
