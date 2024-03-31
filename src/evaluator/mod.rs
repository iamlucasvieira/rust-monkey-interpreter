use crate::ast;
use crate::object::Object;
use anyhow::Result;
use log::{debug, error};
use std::any::TypeId;

pub fn eval(node: &dyn ast::Node) -> Result<Object> {
    debug!("eval: {:?}", node);
    match node.as_any().type_id() {
        id if id == TypeId::of::<ast::Program>() => {
            debug!("eval Program");
            let program = node
                .as_any()
                .downcast_ref::<ast::Program>()
                .ok_or_else(|| anyhow::anyhow!("Expected a Program, got {:?}", id))?;
            program
                .statements
                .iter()
                .map(|statement| eval(statement.as_node()))
                .last()
                .unwrap_or(Ok(Object::Null))
        }

        id if id == TypeId::of::<ast::ExpressionStatement>() => {
            debug!("eval ExpressionStatement");
            let expression_statement = node
                .as_any()
                .downcast_ref::<ast::ExpressionStatement>()
                .ok_or_else(|| anyhow::anyhow!("Expected a ExpressionStatement, got {:?}", id))?;
            eval(expression_statement.expression.as_node())
        }

        id if id == TypeId::of::<ast::IntegerLiteral>() => {
            debug!("eval IntegerLiteral");
            let integer = node
                .as_any()
                .downcast_ref::<ast::IntegerLiteral>()
                .ok_or_else(|| anyhow::anyhow!("Expected a IntegerLiteral, got {:?}", id))?;
            Ok(Object::Integer(integer.value))
        }
        _ => {
            let err_msg = format!("unhandled node: {:?}", node);
            error!("{}", err_msg);
            Err(anyhow::anyhow!("{}", err_msg))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::object::tests::test_integer_object;
    use crate::parser::Parser;
    use log::debug;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    fn test_eval(input: &str) -> Object {
        let mut l = Lexer::new(input);
        let mut p = Parser::new(&mut l);
        let program = p.parse_program().unwrap();
        eval(&program).unwrap()
    }

    #[test]
    fn test_eval_integer_expression() {
        init();
        debug!("test_eval_integer_expression");
        let tests = vec![
            ("5", 5),
            ("10", 10),
            // ("-10", -10),
            // ("-5", -5),
            // ("5 + 5 + 5 + 5 - 10", 10),
            // ("2 * 2 * 2 * 2 * 2", 32),
            // ("-50 + 100 + -50", 0),
            // ("5 * 2 + 10", 20),
            // ("5 + 2 * 10", 25),
            // ("20 + 2 * -10", 0),
            // ("50 / 2 * 2 + 10", 60),
            // ("2 * (5 + 10)", 30),
            // ("3 * 3 * 3 + 10", 37),
            // ("3 * (3 * 3) + 10", 37),
            // ("(5 + 10 * 2 + 15 / 3) * 2 + -10", 50),
        ];

        for (input, expected) in tests {
            let evaluated = test_eval(input);
            test_integer_object(evaluated, expected);
        }
    }
}
