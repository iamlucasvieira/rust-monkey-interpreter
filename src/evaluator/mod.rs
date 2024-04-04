use crate::ast;
use crate::environment::Environment;
use crate::object::{self, Object};
use crate::token;
use anyhow::{self, Result};
use log::{debug, error};

pub fn eval(node: ast::Node, env: &mut Environment) -> Result<Object> {
    debug!("eval: {:?}", node);
    match node {
        ast::Node::Program(program) => eval_program(program, env),
        ast::Node::Statement(stmt) => eval_statement(stmt, env),
        ast::Node::Expression(expr) => eval_expression(expr, env),
    }
}

fn eval_program(program: ast::Program, env: &mut Environment) -> Result<Object> {
    let mut result = Object::Null;

    for stmt in program.statements {
        result = eval(stmt.into(), env)?;
        if let Object::Return(value) = result {
            return Ok(*value);
        }
    }
    Ok(result)
}

fn eval_statement(stmt: ast::Statement, env: &mut Environment) -> Result<Object> {
    match stmt {
        ast::Statement::Expression(expr) => eval(ast::Node::Expression(expr.expression), env),
        ast::Statement::Return(expr) => {
            eval(ast::Node::Expression(ast::Expression::Return(expr)), env)
        }
        ast::Statement::Let(expr) => {
            let value = eval((expr.value).into(), env)?;
            env.set(expr.name.value, value);
            Ok(object::NULL)
        }
    }
}

fn eval_expression(expr: ast::Expression, env: &mut Environment) -> Result<Object> {
    match expr {
        ast::Expression::Integer(literal) => Ok(Object::Integer(literal.value)),
        ast::Expression::Boolean(literal) => eval_boolean(literal),
        ast::Expression::Prefix(literal) => eval_prefix_expression(literal, env),
        ast::Expression::Infix(literal) => eval_infix_expression(literal, env),
        ast::Expression::Block(literal) => eval_block_statement(literal, env),
        ast::Expression::If(literal) => eval_if_expression(literal, env),
        ast::Expression::Return(literal) => eval_return_expression(literal, env),
        ast::Expression::Identifier(literal) => eval_identifier(literal, env),
        _ => {
            error!("eval_expression: {:?}", expr);
            Ok(object::NULL)
        }
    }
}

fn eval_identifier(expr: ast::Identifier, env: &mut Environment) -> Result<Object> {
    match env.get(&expr.value) {
        Some(value) => Ok(value.clone()),
        None => anyhow::bail!(object::Error::IdentifierNotFound(expr.value)),
    }
}

fn eval_block_statement(stmt: ast::BlockStatement, env: &mut Environment) -> Result<Object> {
    let mut result = Object::Null;

    for stmt in stmt.statements {
        result = eval(stmt.into(), env)?;
        if let Object::Return(_) = result {
            return Ok(result);
        }
    }
    Ok(result)
}

fn eval_return_expression(expr: ast::ReturnStatement, env: &mut Environment) -> Result<Object> {
    let value = eval((*expr.return_value).into(), env)?;
    Ok(Object::Return(Box::new(value)))
}

fn eval_if_expression(expr: ast::IfExpression, env: &mut Environment) -> Result<Object> {
    let condition = eval((*expr.condition).into(), env)?;
    if is_truthy(condition) {
        let consequence: ast::Expression = expr.consequence.into();
        eval(consequence.into(), env)
    } else if let Some(alternative) = expr.alternative {
        let alternative: ast::Expression = alternative.into();
        eval(alternative.into(), env)
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

fn eval_prefix_expression(expr: ast::PrefixExpression, env: &mut Environment) -> Result<Object> {
    match expr.operator.to_string().as_str() {
        "!" => {
            let right = eval_expression(*expr.right, env)?;
            eval_bang_operator_expression(right)
        }
        "-" => {
            let right = eval_expression(*expr.right, env)?;
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
        _ => anyhow::bail!(object::Error::UnkownOperator(format!(
            "prefix -{}",
            right.object_type()
        ))),
    }
}

fn eval_infix_expression(expr: ast::InfixExpression, env: &mut Environment) -> Result<Object> {
    let left = eval_expression(*expr.left, env)?;
    let right = eval_expression(*expr.right, env)?;

    match (&left, &right) {
        (Object::Integer(left), Object::Integer(right)) => {
            eval_integer_infix_expression(left, expr.operator.to_string().as_str(), right)
        }
        (_, _) if expr.operator == token::Token::EQ => Ok(object::Object::from_bool(left == right)),
        (_, _) if expr.operator == token::Token::NOTEQ => {
            Ok(object::Object::from_bool(left != right))
        }
        // Case differnt types:
        (_, _) if left.object_type() != right.object_type() => {
            anyhow::bail!(object::Error::TypeMismatch(format!(
                "{} {} {}",
                left.object_type(),
                expr.operator,
                right.object_type()
            )))
        }
        _ => anyhow::bail!(object::Error::UnkownOperator(format!(
            "{} {} {}",
            left.object_type(),
            expr.operator,
            right.object_type()
        ))),
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

    fn test_eval(input: &str) -> Result<Object> {
        let mut l = Lexer::new(input);
        let mut p = Parser::new(&mut l);
        let program = p.parse_program().unwrap();
        let mut env = Environment::new();
        eval(program.into(), &mut env)
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
            let evaluated =
                test_eval(input).expect(&format!("Failed to evaluate input: {}", input));
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
            let evaluated =
                test_eval(input).expect(&format!("Failed to evaluate input: {}", input));
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
            let evaluated =
                test_eval(input).expect(&format!("Failed to evaluate input: {}", input));
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
            let evaluated =
                test_eval(input).expect(&format!("Failed to evaluate input: {}", input));
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
            let evaluated =
                test_eval(input).expect(&format!("Failed to evaluate input: {}", input));
            test_integer_object(evaluated, expected);
        }
    }

    #[test]
    fn test_error_handling() {
        init();
        debug!("test_error_handling");
        let tests = vec![
            (
                "5 + true;",
                object::Error::TypeMismatch("INTEGER + BOOLEAN".to_string()),
            ),
            (
                "5 + true; 5;",
                object::Error::TypeMismatch("INTEGER + BOOLEAN".to_string()),
            ),
            (
                "-true",
                object::Error::UnkownOperator("prefix -BOOLEAN".to_string()),
            ),
            (
                "true + false;",
                object::Error::UnkownOperator("BOOLEAN + BOOLEAN".to_string()),
            ),
            (
                "5; true + false; 5",
                object::Error::UnkownOperator("BOOLEAN + BOOLEAN".to_string()),
            ),
            (
                "if (10 > 1) { true + false; }",
                object::Error::UnkownOperator("BOOLEAN + BOOLEAN".to_string()),
            ),
            (
                r#"
                if (10 > 1) {
                    if (10 > 1) {
                        return true + false;
                    }
                    return 1;
                }
                "#,
                object::Error::UnkownOperator("BOOLEAN + BOOLEAN".to_string()),
            ),
            (
                "foobar",
                object::Error::IdentifierNotFound("foobar".to_string()),
            ),
        ];
        for (input, expected) in tests {
            let err = test_eval(input)
                .unwrap_err()
                .downcast::<object::Error>()
                .unwrap();

            assert_eq!(err, expected);
        }
    }

    #[test]
    fn test_let_statements() {
        init();
        debug!("test_let_statements");
        let tests = vec![
            ("let a = 5; a;", 5),
            ("let a = 5 * 5; a;", 25),
            ("let a = 5; let b = a; b;", 5),
            ("let a = 5; let b = a; let c = a + b + 5; c;", 15),
        ];

        for (input, expected) in tests {
            let evaluated =
                test_eval(input).expect(&format!("Failed to evaluate input: {}", input));
            test_integer_object(evaluated, expected);
        }
    }
}
