use crate::ast;
use crate::builtins::Builtins;
use crate::environment::Environment;
use crate::object::{self, HashKey, Object};
use crate::token;
use anyhow::{self, Result};
use log::{debug, error};
use std::cell::RefCell;
use std::rc::Rc;
use std::str::FromStr;

pub fn eval(node: ast::Node, env: Rc<RefCell<Environment>>) -> Result<Rc<Object>> {
    debug!("eval: {:?}", node);
    match node {
        ast::Node::Program(program) => eval_program(program, Rc::clone(&env)),
        ast::Node::Statement(stmt) => eval_statement(stmt, Rc::clone(&env)),
        ast::Node::Expression(expr) => eval_expression(expr, Rc::clone(&env)),
    }
}

fn eval_program(program: ast::Program, env: Rc<RefCell<Environment>>) -> Result<Rc<Object>> {
    let mut result = Rc::new(Object::Null);

    for stmt in program.statements {
        result = eval(stmt.into(), Rc::clone(&env))?;
        if let Object::Return(value) = &*result {
            return Ok(Rc::clone(value));
        }
    }
    Ok(result)
}

fn eval_statement(stmt: ast::Statement, env: Rc<RefCell<Environment>>) -> Result<Rc<Object>> {
    match stmt {
        ast::Statement::Expression(expr) => eval(ast::Node::Expression(expr.expression), env),
        ast::Statement::Return(expr) => {
            eval(ast::Node::Expression(ast::Expression::Return(expr)), env)
        }
        ast::Statement::Let(expr) => {
            let value = eval((expr.value).into(), Rc::clone(&env))?;
            env.borrow_mut().set(expr.name.value, value);
            Ok(Rc::new(object::NULL))
        }
    }
}

fn eval_expression(expr: ast::Expression, env: Rc<RefCell<Environment>>) -> Result<Rc<Object>> {
    match expr {
        ast::Expression::Integer(literal) => Ok(Rc::new(Object::Integer(literal.value))),
        ast::Expression::String(literal) => Ok(Rc::new(Object::String(literal.value))),
        ast::Expression::Boolean(literal) => eval_boolean(literal),
        ast::Expression::Prefix(literal) => eval_prefix_expression(literal, Rc::clone(&env)),
        ast::Expression::Infix(literal) => eval_infix_expression(literal, Rc::clone(&env)),
        ast::Expression::Block(literal) => eval_block_statement(literal, Rc::clone(&env)),
        ast::Expression::If(literal) => eval_if_expression(literal, Rc::clone(&env)),
        ast::Expression::Return(literal) => eval_return_expression(literal, Rc::clone(&env)),
        ast::Expression::Identifier(literal) => eval_identifier(literal, Rc::clone(&env)),
        ast::Expression::Function(literal) => Ok(Rc::new(Object::Function {
            parameters: literal.parameters,
            body: Rc::new(RefCell::new(literal.body)),
            env: Rc::clone(&env),
        })),
        ast::Expression::Call(literal) => eval_function_call(literal, Rc::clone(&env)),
        ast::Expression::Array(literal) => {
            let elements = eval_expressions(literal.elements, Rc::clone(&env))?;
            Ok(Rc::new(Object::Array(elements)))
        }
        ast::Expression::Index(literal) => eval_index_expression(literal, Rc::clone(&env)),
        ast::Expression::Hash(literal) => eval_hash_literal(literal, Rc::clone(&env)),
    }
}

fn eval_expressions(
    exprs: Vec<ast::Expression>,
    env: Rc<RefCell<Environment>>,
) -> Result<Vec<Rc<Object>>> {
    exprs
        .into_iter()
        .map(|expr| eval(expr.into(), Rc::clone(&env)))
        .collect::<Result<Vec<Rc<Object>>>>()
}

fn eval_function_call(
    expr: ast::CallExpression,
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<Object>> {
    let function = eval((*expr.function).into(), Rc::clone(&env))?;
    let args = eval_expressions(expr.arguments, Rc::clone(&env))?;
    apply_function(function, args)
}

fn eval_index_expression(
    expr: ast::IndexExpression,
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<Object>> {
    let left = eval((*expr.left).into(), Rc::clone(&env))?;
    let index = eval((*expr.index).into(), Rc::clone(&env))?;

    match (&*left, &*index) {
        (Object::Array(elements), Object::Integer(i)) => {
            if *i < 0 || *i >= elements.len() as i64 {
                return Ok(Rc::new(object::NULL));
            }
            Ok(Rc::clone(&elements[*i as usize]))
        }
        _ => anyhow::bail!(object::Error::UnkownOperator(format!(
            "{}[{}]",
            left.object_type(),
            index.object_type()
        ))),
    }
}

fn eval_hash_literal(expr: ast::HashLiteral, env: Rc<RefCell<Environment>>) -> Result<Rc<Object>> {
    let mut pairs = std::collections::HashMap::new();

    for (key_expr, value_expr) in expr.pairs {
        let key = eval((*key_expr).into(), Rc::clone(&env))?;
        let value = eval((*value_expr).into(), Rc::clone(&env))?;
        let key_hash = (*key).hash_key()?;
        pairs.insert(key_hash, (key, value));
    }
    Ok(Rc::new(Object::Hash(pairs)))
}
fn apply_function(func: Rc<Object>, args: Vec<Rc<Object>>) -> Result<Rc<Object>> {
    match &*func {
        Object::Function {
            parameters,
            body,
            env,
        } => {
            let mut extended_env = Environment::new_enclosed(Rc::clone(env));
            for (param, arg) in parameters.iter().zip(args) {
                extended_env.set(param.value.clone(), arg);
            }
            let borrowed_body = body.borrow();
            let expr: ast::Expression = (*borrowed_body).clone().into();

            eval(expr.into(), Rc::new(RefCell::new(extended_env)))
        }
        Object::BuiltInFunction(builtin) => builtin.call(args),
        _ => anyhow::bail!(object::Error::UnkownOperator(format!(
            "not a function: {}",
            func.object_type()
        ))),
    }
}

fn eval_identifier(expr: ast::Identifier, env: Rc<RefCell<Environment>>) -> Result<Rc<Object>> {
    if let Some(value) = env.borrow().get(&expr.value) {
        Ok(value)
    } else if let Ok(builtin) = Builtins::from_str(&expr.value) {
        Ok(Rc::new(Object::BuiltInFunction(builtin)))
    } else {
        anyhow::bail!(object::Error::IdentifierNotFound(expr.value))
    }
}

fn eval_block_statement(
    stmt: ast::BlockStatement,
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<Object>> {
    let mut result = Rc::new(Object::Null);

    for stmt in stmt.statements {
        result = eval(stmt.into(), Rc::clone(&env))?;
        if let Object::Return(_) = &*result {
            return Ok(result);
        }
    }
    Ok(result)
}

fn eval_return_expression(
    expr: ast::ReturnStatement,
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<Object>> {
    let value = eval((*expr.return_value).into(), Rc::clone(&env))?;
    Ok(Rc::new(Object::Return(Box::new(value))))
}

fn eval_if_expression(
    expr: ast::IfExpression,
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<Object>> {
    let condition = eval((*expr.condition).into(), Rc::clone(&env))?;
    if is_truthy(&condition) {
        let consequence: ast::Expression = expr.consequence.into();
        eval(consequence.into(), Rc::clone(&env))
    } else if let Some(alternative) = expr.alternative {
        let alternative: ast::Expression = alternative.into();
        eval(alternative.into(), env)
    } else {
        Ok(Rc::new(object::NULL))
    }
}

fn is_truthy(obj: &Object) -> bool {
    match *obj {
        object::NULL => false,
        object::TRUE => true,
        object::FALSE => false,
        _ => true,
    }
}

fn eval_boolean(expr: ast::Boolean) -> Result<Rc<Object>> {
    Ok(Rc::new(object::Object::from_bool(expr.value)))
}

fn eval_prefix_expression(
    expr: ast::PrefixExpression,
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<Object>> {
    match expr.operator.to_string().as_str() {
        "!" => {
            let right = eval_expression(*expr.right, env)?;
            eval_bang_operator_expression(&right)
        }
        "-" => {
            let right = eval_expression(*expr.right, env)?;
            eval_minus_prefix_operator_expression(&right)
        }
        _ => {
            error!("eval_prefix_expression: {:?}", expr);
            Ok(Rc::new(object::NULL))
        }
    }
}

fn eval_bang_operator_expression(right: &Object) -> Result<Rc<Object>> {
    let result = match *right {
        object::TRUE => object::FALSE,
        object::FALSE => object::TRUE,
        object::NULL => object::TRUE,
        _ => object::FALSE,
    };
    Ok(Rc::new(result))
}

fn eval_minus_prefix_operator_expression(right: &Object) -> Result<Rc<Object>> {
    match *right {
        Object::Integer(value) => Ok(Rc::new(Object::Integer(-value))),
        _ => anyhow::bail!(object::Error::UnkownOperator(format!(
            "prefix -{}",
            right.object_type()
        ))),
    }
}

fn eval_infix_expression(
    expr: ast::InfixExpression,
    env: Rc<RefCell<Environment>>,
) -> Result<Rc<Object>> {
    let left = eval_expression(*expr.left, Rc::clone(&env))?;
    let right = eval_expression(*expr.right, Rc::clone(&env))?;

    match (&*left, &*right) {
        (Object::Integer(left), Object::Integer(right)) => {
            eval_integer_infix_expression(left, expr.operator.to_string().as_str(), right)
        }
        (Object::String(left), Object::String(right)) => {
            eval_string_infix_expression(left, expr.operator.to_string().as_str(), right)
        }
        (_, _) if expr.operator == token::Token::EQ => {
            Ok(Rc::new(object::Object::from_bool(left == right)))
        }
        (_, _) if expr.operator == token::Token::NOTEQ => {
            Ok(Rc::new(object::Object::from_bool(left != right)))
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

fn eval_integer_infix_expression(left: &i64, operator: &str, right: &i64) -> Result<Rc<Object>> {
    let result = match operator {
        "+" => Object::Integer(left + right),
        "-" => Object::Integer(left - right),
        "*" => Object::Integer(left * right),
        "/" => Object::Integer(left / right),
        "<" => object::Object::from_bool(left < right),
        ">" => object::Object::from_bool(left > right),
        "==" => object::Object::from_bool(left == right),
        "!=" => object::Object::from_bool(left != right),
        _ => {
            anyhow::bail!(object::Error::UnkownOperator(format!(
                "INTEGER {} INTEGER",
                operator
            )))
        }
    };
    Ok(Rc::new(result))
}

fn eval_string_infix_expression(left: &str, operator: &str, right: &str) -> Result<Rc<Object>> {
    let result = match operator {
        "+" => Object::String(format!("{}{}", left, right)),
        _ => {
            anyhow::bail!(object::Error::UnkownOperator(format!(
                "STRING {} STRING",
                operator
            )))
        }
    };
    Ok(Rc::new(result))
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

    fn test_eval(input: &str) -> Result<Rc<Object>> {
        let mut l = Lexer::new(input);
        let mut p = Parser::new(&mut l);
        let program = p.parse_program().unwrap();
        let env = Rc::new(RefCell::new(Environment::new()));
        eval(program.into(), env)
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
                test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));
            test_integer_object(&evaluated, expected);
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
                test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));
            test_boolean_object(&evaluated, expected);
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
                test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));
            test_boolean_object(&evaluated, expected);
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
                test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));
            match expected {
                Some(value) => test_integer_object(&evaluated, value),
                None => test_null_object(&evaluated),
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
                test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));
            test_integer_object(&evaluated, expected);
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
                test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));
            test_integer_object(&evaluated, expected);
        }
    }

    #[test]
    fn test_function_object() {
        init();
        debug!("test_function_object");
        let input = "fn(x) { x + 2; }";
        let evaluated = test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));

        match &*evaluated {
            Object::Function {
                parameters, body, ..
            } => {
                assert_eq!(parameters.len(), 1);
                assert_eq!(parameters[0].value, "x");
                let body = body.borrow();
                assert_eq!(body.to_string(), "(x + 2)");
            }
            _ => panic!("object is not Function. got={}", evaluated.object_type()),
        }
    }

    #[test]
    fn test_function_application() {
        init();
        debug!("test_function_application");
        let tests = vec![
            ("let identity = fn(x) { x; }; identity(5);", 5),
            ("let identity = fn(x) { return x; }; identity(5);", 5),
            ("let double = fn(x) { x * 2; }; double(5);", 10),
            ("let add = fn(x, y) { x + y; }; add(5, 5);", 10),
            ("let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));", 20),
            ("fn(x) { x; }(5)", 5),
        ];

        for (input, expected) in tests {
            let evaluated =
                test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));
            test_integer_object(&evaluated, expected);
        }
    }

    #[test]
    fn test_closures() {
        init();
        debug!("test_closures");
        let input = r#"
        let newAdder = fn(x) {
            fn(y) { x + y };
        };
        let addTwo = newAdder(2);
        addTwo(3);
        "#;
        let evaluated = test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));
        test_integer_object(&evaluated, 5);
    }

    #[test]
    fn test_string_literal() {
        init();
        debug!("test_string_literal");
        let input = r#""Hello, World!""#;
        let evaluated = test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));
        match &*evaluated {
            Object::String(value) => assert_eq!(value, "Hello, World!"),
            _ => panic!("object is not String. got={}", evaluated.object_type()),
        }
    }

    #[test]
    fn test_string_concatenation() {
        init();
        debug!("test_string_concatenation");
        let input = r#""Hello" + " " + "World!""#;
        let evaluated = test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));
        match &*evaluated {
            Object::String(value) => assert_eq!(value, "Hello World!"),
            _ => panic!("object is not String. got={}", evaluated.object_type()),
        }
    }

    #[test]
    fn test_error_handling_string_concatenation() {
        init();
        debug!("test_error_handling_string_concatenation");
        let input = r#""Hello" + " " + 1"#;
        let err = test_eval(input)
            .unwrap_err()
            .downcast::<object::Error>()
            .unwrap();
        assert_eq!(
            err,
            object::Error::TypeMismatch("STRING + INTEGER".to_string())
        );
    }

    #[test]
    fn test_builtin_functions() {
        init();
        debug!("test_builtin_functions");
        let tests = vec![
            (r#"len("")"#, Object::Integer(0)),
            (r#"len("four")"#, Object::Integer(4)),
            (r#"len("hello world")"#, Object::Integer(11)),
        ];

        for (input, expected) in tests {
            let evaluated =
                test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));
            assert_eq!(*evaluated, expected);
        }
    }

    #[test]
    fn test_builtin_functions_errors() {
        init();
        debug!("test_builtin_functions_errors");
        let tests = vec![
            (r#"len(1)"#, "argument to `len` not supported, got INTEGER"),
            (
                r#"len("one", "two")"#,
                "wrong number of arguments. got=2, want=1",
            ),
        ];

        for (input, expected) in tests {
            let err = test_eval(input)
                .expect_err(&format!("Failed to evaluate input: {}", input))
                .downcast::<object::Error>()
                .expect("Failed to downcast to object::Error");
            assert_eq!(err, object::Error::TypeMismatch(expected.to_string()));
        }
    }

    #[test]
    fn test_array_literals() {
        init();
        debug!("test_array_literals");
        let input = "[1, 2 * 2, 3 + 3]";
        let evaluated = test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));
        match &*evaluated {
            Object::Array(elements) => {
                assert_eq!(elements.len(), 3);
                test_integer_object(&elements[0], 1);
                test_integer_object(&elements[1], 4);
                test_integer_object(&elements[2], 6);
            }
            _ => panic!("object is not Array. got={}", evaluated.object_type()),
        }
    }

    #[test]
    fn test_array_index_expressions() {
        init();
        debug!("test_array_index_expressions");
        let tests = vec![
            ("[1, 2, 3][0]", Object::Integer(1)),
            ("[1, 2, 3][1]", Object::Integer(2)),
            ("[1, 2, 3][2]", Object::Integer(3)),
            ("let i = 0; [1][i];", Object::Integer(1)),
            ("[1, 2, 3][1 + 1];", Object::Integer(3)),
            ("let myArray = [1, 2, 3]; myArray[2];", Object::Integer(3)),
            (
                "let myArray = [1, 2, 3]; myArray[0] + myArray[1] + myArray[2];",
                Object::Integer(6),
            ),
            (
                "let myArray = [1, 2, 3]; let i = myArray[0]; myArray[i]",
                Object::Integer(2),
            ),
            ("[1, 2, 3][3]", object::NULL),
            ("[1, 2, 3][-1]", object::NULL),
        ];

        for (input, expected) in tests {
            let evaluated =
                test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));

            if let Object::Integer(i) = expected {
                test_integer_object(&evaluated, i);
            } else {
                test_null_object(&evaluated);
            }
        }
    }

    #[test]
    fn test_hash_literals() {
        init();
        debug!("test_hash_literals");
        let input = r#"let two = "two";
        {
            "one": 10 - 9,
            two: 1 + 1,
            "thr" + "ee": 6 / 2,
            4: 4,
            true: 5,
            false: 6
        }"#;
        let evaluated = test_eval(input).unwrap_or_else(|_| panic!("Failed to evaluate input: {}", input));

        let expected = vec![
            (Object::String("one".to_string()).hash_key(), 1),
            (Object::String("two".to_string()).hash_key(), 2),
            (Object::String("three".to_string()).hash_key(), 3),
            (Object::Integer(4).hash_key(), 4),
            (object::TRUE.hash_key(), 5),
            (object::FALSE.hash_key(), 6),
        ];

        match &*evaluated {
            Object::Hash(pairs) => {
                assert_eq!(
                    pairs.len(),
                    expected.len(),
                    "Hash has wrong number of pairs"
                );
                for (key, value) in expected {
                    let (_, pair_value) = pairs.get(&key.unwrap()).unwrap();
                    test_integer_object(pair_value, value);
                }
            }
            _ => panic!("object is not Hash. got={}", evaluated.object_type()),
        }
    }
}
