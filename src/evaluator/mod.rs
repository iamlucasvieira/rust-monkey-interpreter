use crate::ast;
use crate::object::{self, Object};
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
    program
        .statements
        .into_iter()
        .map(|stmt| eval(stmt.into()))
        .last()
        .unwrap_or(Ok(Object::Null))
}

fn eval_statement(stmt: ast::Statement) -> Result<Object> {
    match stmt {
        ast::Statement::Expression(expr) => eval(ast::Node::Expression(expr.expression)),
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
        _ => {
            error!("eval_expression: {:?}", expr);
            Ok(object::NULL)
        }
    }
}

fn eval_boolean(expr: ast::Boolean) -> Result<Object> {
    match expr.value {
        true => Ok(object::TRUE),
        false => Ok(object::FALSE),
    }
}

fn eval_prefix_expression(expr: ast::PrefixExpression) -> Result<Object> {
    match expr.operator.to_string().as_str() {
        "!" => {
            let right = eval_expression(*expr.right)?;
            Ok(eval_bang_operator_expression(right))
        }
        "-" => {
            let right = eval_expression(*expr.right)?;
            Ok(eval_minus_prefix_operator_expression(right))
        }
        _ => {
            error!("eval_prefix_expression: {:?}", expr);
            Ok(object::NULL)
        }
    }
}

fn eval_bang_operator_expression(right: Object) -> Object {
    match right {
        object::TRUE => object::FALSE,
        object::FALSE => object::TRUE,
        object::NULL => object::TRUE,
        _ => object::FALSE,
    }
}

fn eval_minus_prefix_operator_expression(right: Object) -> Object {
    match right {
        Object::Integer(value) => Object::Integer(-value),
        _ => object::NULL,
    }
}

fn eval_infix_expression(expr: ast::InfixExpression) -> Result<Object> {
    let left = eval_expression(*expr.left)?;
    let right = eval_expression(*expr.right)?;

    match (&left, &right) {
        (Object::Integer(left), Object::Integer(right)) => match expr.operator.to_string().as_str()
        {
            "+" => Ok(Object::Integer(left + right)),
            "-" => Ok(Object::Integer(left - right)),
            "*" => Ok(Object::Integer(left * right)),
            "/" => Ok(Object::Integer(left / right)),
            _ => {
                error!(
                    "Invalid operator '{:?}' for integers",
                    expr.operator.to_string()
                );
                Ok(object::NULL)
            }
        },
        _ => {
            error!(
                "Invalid infix expression: left={:?}, right={:?}",
                left, right
            );
            Ok(object::NULL)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::object::tests::{test_boolean_object, test_integer_object};
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
            // ("1 < 2", true),
            // ("1 > 2", false),
            // ("1 < 1", false),
            // ("1 > 1", false),
            // ("1 == 1", true),
            // ("1 != 1", false),
            // ("1 == 2", false),
            // ("1 != 2", true),
            // ("true == true", true),
            // ("false == false", true),
            // ("true == false", false),
            // ("true != false", true),
            // ("false != true", true),
            // ("(1 < 2) == true", true),
            // ("(1 < 2) == false", false),
            // ("(1 > 2) == true", false),
            // ("(1 > 2) == false", true),
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
}
