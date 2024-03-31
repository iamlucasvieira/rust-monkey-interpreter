use anyhow::Result;
use std::fmt;

#[derive(Debug)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    Null,
}

impl Object {
    fn object_type(&self) -> &'static str {
        match self {
            Object::Integer(_) => "INTEGER",
            Object::Boolean(_) => "BOOLEAN",
            Object::Null => "NULL",
        }
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Object::Integer(value) => write!(f, "{}", value),
            Object::Boolean(value) => write!(f, "{}", value),
            Object::Null => write!(f, "null"),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    pub fn test_integer_object(obj: Object, expected: i64) {
        match obj {
            Object::Integer(value) => assert_eq!(value, expected),
            _ => panic!("object is not Integer. got={}", obj.object_type()),
        }
    }

    fn test_boolean_object(obj: Object, expected: bool) {
        match obj {
            Object::Boolean(value) => assert_eq!(value, expected),
            _ => panic!("object is not Boolean. got={}", obj.object_type()),
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
            test_integer_object(obj, expected);
        }
    }

    #[test]
    fn test_boolean_objects() {
        let tests = vec![
            (Object::Boolean(true), true),
            (Object::Boolean(false), false),
        ];

        for (obj, expected) in tests {
            test_boolean_object(obj, expected);
        }
    }

    #[test]
    fn test_null_object() {
        let obj = Object::Null;
        assert_eq!(obj.object_type(), "NULL");
    }
}
