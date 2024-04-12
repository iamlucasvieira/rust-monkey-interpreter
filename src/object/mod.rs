use crate::ast;
use crate::builtins::Builtins;
use crate::environment::Environment;
use anyhow::Result;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::hash::DefaultHasher;
use std::hash::Hash;
use std::hash::Hasher;
use std::rc::Rc;

pub const TRUE: Object = Object::Boolean(true);
pub const FALSE: Object = Object::Boolean(false);
pub const NULL: Object = Object::Null;

pub trait HashKey {
    fn hash_key(&self) -> Result<u64>;
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Object {
    Integer(i64),
    String(String),
    Boolean(bool),
    Null,
    Return(Box<Rc<Object>>),
    Function {
        parameters: Vec<ast::Identifier>,
        body: Rc<RefCell<ast::BlockStatement>>,
        env: Rc<RefCell<Environment>>,
    },
    BuiltInFunction(Builtins),
    Array(Vec<Rc<Object>>),
    Hash(HashMap<u64, (Rc<Object>, Rc<Object>)>),
}

impl HashKey for Object {
    fn hash_key(&self) -> Result<u64> {
        match self {
            Object::Integer(value) => Ok(*value as u64),
            Object::Boolean(value) => {
                if *value {
                    Ok(1)
                } else {
                    Ok(0)
                }
            }
            Object::String(value) => {
                let mut hasher = DefaultHasher::new();
                (*value).hash(&mut hasher);
                Ok(hasher.finish())
            }
            _ => anyhow::bail!("unusable as hash key"),
        }
    }
}

impl Object {
    pub fn object_type(&self) -> &'static str {
        match self {
            Object::Integer(_) => "INTEGER",
            Object::String(_) => "STRING",
            Object::Boolean(_) => "BOOLEAN",
            Object::Null => "NULL",
            Object::Return(_) => "RETURN",
            Object::Function { .. } => "FUNCTION",
            Object::BuiltInFunction(_) => "BUILTIN_FUNCTION",
            Object::Array(_) => "ARRAY",
            Object::Hash(..) => "HASH",
        }
    }

    pub fn from_bool(value: bool) -> Object {
        match value {
            true => TRUE,
            false => FALSE,
        }
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Object::Integer(value) => write!(f, "{}", value),
            Object::String(value) => write!(f, "\'{}\'", value),
            Object::Boolean(value) => write!(f, "{}", value),
            Object::Null => write!(f, "null"),
            Object::Return(value) => write!(f, "{}", value),
            Object::Function {
                parameters, body, ..
            } => {
                let params: Vec<String> = parameters.iter().map(|p| p.to_string()).collect();
                let body = body.borrow().to_string();
                write!(f, "fn({}) {{\n{}\n}}", params.join(", "), body)
            }
            Object::BuiltInFunction(_) => write!(f, "Builtin Function"),
            Object::Array(elements) => {
                let elements: Vec<String> = elements.iter().map(|e| e.to_string()).collect();
                write!(f, "[{}]", elements.join(", "))
            }
            Object::Hash(pairs) => {
                let pairs: Vec<String> = pairs
                    .iter()
                    .map(|(_, (k, v))| format!("{}: {}", k, v))
                    .collect();
                write!(f, "{{{}}}", pairs.join(", "))
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    TypeMismatch(String),
    UnkownOperator(String),
    IdentifierNotFound(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::TypeMismatch(msg) => write!(f, "TypeMismatch: {}", msg),
            Error::UnkownOperator(msg) => write!(f, "UnkownOperator: {}", msg),
            Error::IdentifierNotFound(msg) => write!(f, "IdentifierNotFound: {}", msg),
        }
    }
}

impl std::error::Error for Error {}
#[cfg(test)]
pub mod tests {
    use super::*;

    pub fn test_integer_object(obj: &Object, expected: i64) {
        match obj {
            Object::Integer(value) => assert_eq!(*value, expected),
            Object::Return(value) => test_integer_object(&**value, expected),
            _ => panic!("object is not Integer. got={}", obj.object_type()),
        }
    }

    pub fn test_boolean_object(obj: &Object, expected: bool) {
        match obj {
            Object::Boolean(value) => assert_eq!(*value, expected),
            _ => panic!("object is not Boolean. got={}", obj.object_type()),
        }
    }

    pub fn test_null_object(obj: &Object) {
        match obj {
            Object::Null => (),
            _ => panic!("object is not Null. got={}", obj.object_type()),
        }
    }

    pub fn test_error(err: Error, expected: &str) {
        match err {
            Error::TypeMismatch(msg) => assert_eq!(msg, expected),
            Error::UnkownOperator(msg) => assert_eq!(msg, expected),
            Error::IdentifierNotFound(msg) => assert_eq!(msg, expected),
        }
    }

    #[test]
    fn test_integer_objects() {
        let tests = vec![
            (Object::Integer(5), 5),
            (Object::Integer(10), 10),
            (Object::Integer(-5), -5),
            (Object::Integer(-10), -10),
        ];

        for (obj, expected) in tests {
            test_integer_object(&obj, expected);
        }
    }

    #[test]
    fn test_boolean_objects() {
        let tests = vec![
            (Object::Boolean(true), true),
            (Object::Boolean(false), false),
        ];

        for (obj, expected) in tests {
            test_boolean_object(&obj, expected);
        }
    }

    #[test]
    fn test_null_objects() {
        test_null_object(&Object::Null);
    }

    #[test]
    fn test_errors() {
        let tests = vec![
            (Error::TypeMismatch("foo".to_string()), "foo"),
            (Error::UnkownOperator("bar".to_string()), "bar"),
        ];

        for (err, expected) in tests {
            test_error(err, expected);
        }
    }

    #[test]
    fn test_string_hash_key() {
        let hello1 = Object::String("Hello World".to_string());
        let hello2 = Object::String("Hello World".to_string());
        let diff1 = Object::String("My name is johnny".to_string());
        let diff2 = Object::String("My name is johnny".to_string());

        assert_eq!(
            hello1.hash_key().unwrap(),
            hello2.hash_key().unwrap(),
            "strings with same content have different hash keys"
        );
        assert_eq!(
            diff1.hash_key().unwrap(),
            diff2.hash_key().unwrap(),
            "strings with same content have different hash keys"
        );
        assert_ne!(
            hello1.hash_key().unwrap(),
            diff1.hash_key().unwrap(),
            "strings with different content have same hash keys"
        );
    }
}
