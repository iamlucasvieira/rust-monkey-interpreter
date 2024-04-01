use std::fmt;

pub const TRUE: Object = Object::Boolean(true);
pub const FALSE: Object = Object::Boolean(false);
pub const NULL: Object = Object::Null;

#[derive(Debug, PartialEq, Eq)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    Null,
    Return(Box<Object>),
}

impl Object {
    fn object_type(&self) -> &'static str {
        match self {
            Object::Integer(_) => "INTEGER",
            Object::Boolean(_) => "BOOLEAN",
            Object::Null => "NULL",
            Object::Return(_) => "RETURN",
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
            Object::Boolean(value) => write!(f, "{}", value),
            Object::Null => write!(f, "null"),
            Object::Return(value) => write!(f, "{}", value),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    pub fn test_integer_object(obj: Object, expected: i64) {
        match obj {
            Object::Integer(value) => assert_eq!(value, expected),
            Object::Return(value) => test_integer_object(*value, expected),
            _ => panic!("object is not Integer. got={}", obj.object_type()),
        }
    }

    pub fn test_boolean_object(obj: Object, expected: bool) {
        match obj {
            Object::Boolean(value) => assert_eq!(value, expected),
            _ => panic!("object is not Boolean. got={}", obj.object_type()),
        }
    }

    pub fn test_null_object(obj: Object) {
        match obj {
            Object::Null => (),
            _ => panic!("object is not Null. got={}", obj.object_type()),
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
    fn test_null_objects() {
        test_null_object(Object::Null);
    }
}
