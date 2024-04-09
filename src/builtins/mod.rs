use crate::object::{Error, Object};
use anyhow::{self, Result};
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Builtins {
    Len,
}

impl Builtins {
    pub fn call(&self, args: Vec<Rc<Object>>) -> Result<Rc<Object>> {
        match self {
            Builtins::Len => builtin_len(args),
        }
    }
}

impl std::str::FromStr for Builtins {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Builtins> {
        match s {
            "len" => Ok(Builtins::Len),
            _ => anyhow::bail!("unknown builtin function: {}", s),
        }
    }
}

fn builtin_len(args: Vec<Rc<Object>>) -> Result<Rc<Object>> {
    if args.len() != 1 {
        return Err(Error::TypeMismatch(format!(
            "wrong number of arguments. got={}, want=1",
            args.len()
        ))
        .into());
    }

    match &*args[0] {
        Object::String(s) => Ok(Rc::new(Object::Integer(s.len() as i64))),
        _ => Err(Error::TypeMismatch(format!(
            "argument to `len` not supported, got {}",
            args[0].object_type()
        ))
        .into()),
    }
}
