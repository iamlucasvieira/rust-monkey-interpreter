use crate::object::{Error, Object};
use anyhow::{self, Result};
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Builtins {
    Len,
    First,
    Last,
    Rest,
    Push,
}

impl Builtins {
    pub fn call(&self, args: Vec<Rc<Object>>) -> Result<Rc<Object>> {
        match self {
            Builtins::Len => builtin_len(args),
            Builtins::First => builtin_first(args),
            Builtins::Last => builtin_last(args),
            Builtins::Rest => builtin_rest(args),
            Builtins::Push => builtin_push(args),
        }
    }
}

impl std::str::FromStr for Builtins {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Builtins> {
        match s {
            "len" => Ok(Builtins::Len),
            "first" => Ok(Builtins::First),
            "last" => Ok(Builtins::Last),
            "rest" => Ok(Builtins::Rest),
            "push" => Ok(Builtins::Push),
            _ => anyhow::bail!("unknown builtin function: {}", s),
        }
    }
}

fn validate_args(args: &[Rc<Object>], expected_n: usize) -> Result<()> {
    if args.len() != expected_n {
        anyhow::bail!(Error::TypeMismatch(format!(
            "wrong number of arguments. got={}, want=1",
            args.len()
        )))
    }
    Ok(())
}
fn builtin_len(args: Vec<Rc<Object>>) -> Result<Rc<Object>> {
    validate_args(&args, 1)?;

    match &*args[0] {
        Object::String(s) => Ok(Rc::new(Object::Integer(s.len() as i64))),
        Object::Array(a) => Ok(Rc::new(Object::Integer(a.len() as i64))),
        _ => anyhow::bail!(Error::TypeMismatch(format!(
            "argument to `len` not supported, got {}",
            args[0].object_type()
        ))),
    }
}

fn builtin_first(args: Vec<Rc<Object>>) -> Result<Rc<Object>> {
    validate_args(&args, 1)?;

    match &*args[0] {
        Object::Array(a) => Ok(Rc::clone(&a[0])),
        _ => anyhow::bail!(Error::TypeMismatch(format!(
            "argument to `first` not supported, got {}",
            args[0].object_type()
        ))),
    }
}

fn builtin_last(args: Vec<Rc<Object>>) -> Result<Rc<Object>> {
    validate_args(&args, 1)?;

    match &*args[0] {
        Object::Array(a) => Ok(Rc::clone(&a[a.len() - 1])),
        _ => anyhow::bail!(Error::TypeMismatch(format!(
            "argument to `last` not supported, got {}",
            args[0].object_type()
        ))),
    }
}

fn builtin_rest(args: Vec<Rc<Object>>) -> Result<Rc<Object>> {
    validate_args(&args, 1)?;

    match &*args[0] {
        Object::Array(a) => {
            let rest_elements: Vec<Rc<Object>> = a.iter().skip(1).cloned().collect();
            Ok(Rc::new(Object::Array(rest_elements)))
        }
        _ => anyhow::bail!(Error::TypeMismatch(format!(
            "argument to `rest` not supported, got {}",
            args[0].object_type()
        ))),
    }
}

fn builtin_push(args: Vec<Rc<Object>>) -> Result<Rc<Object>> {
    validate_args(&args, 2)?;

    match &*args[0] {
        Object::Array(a) => {
            let mut new_array: Vec<Rc<Object>> = a.to_vec();
            new_array.push(Rc::clone(&args[1]));
            Ok(Rc::new(Object::Array(new_array)))
        }
        _ => anyhow::bail!(Error::TypeMismatch(format!(
            "argument to `push` not supported, got {}",
            args[0].object_type()
        ))),
    }
}
