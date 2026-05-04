use std::sync::Arc;

use anyhow::{Context, Result, anyhow, ensure};

use crate::object::{Builtin, Object, create_null};

pub static BUILTINS: [(&str, Builtin); 6] = [
    ("len", Builtin::new(len)),
    ("puts", Builtin::new(puts)),
    ("first", Builtin::new(first)),
    ("last", Builtin::new(last)),
    ("rest", Builtin::new(rest)),
    ("push", Builtin::new(push)),
];

pub fn get_builtin_by_name(name: &str) -> Option<&'static Builtin> {
    for (_name, builtin) in BUILTINS.iter() {
        if *_name == name {
            return Some(builtin);
        }
    }

    None
}

pub fn len(args: &[Arc<Object>]) -> Result<Arc<Object>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = &*args[0];

    match arg {
        Object::String(s) => Ok(Arc::new(Object::int(s.read().unwrap().value.len() as i64))),
        Object::Array(a) => Ok(Arc::new(Object::int(a.read().unwrap().array.len() as i64))),
        _ => Err(anyhow!("{arg:?} is not supported by len.")),
    }
}

pub fn first(args: &[Arc<Object>]) -> Result<Arc<Object>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = &*args[0];

    match arg {
        Object::Array(array) => Ok(array
            .read()
            .unwrap()
            .array
            .first()
            .context("the array is empty.")?
            .clone()),
        _ => Err(anyhow!("{arg:?} is not supported by first.")),
    }
}

pub fn last(args: &[Arc<Object>]) -> Result<Arc<Object>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = &*args[0];

    match arg {
        Object::Array(array) => Ok(array
            .read()
            .unwrap()
            .array
            .last()
            .context("the array is empty.")?
            .clone()),
        _ => Err(anyhow!("{arg:?} is not supported by last.")),
    }
}

pub fn rest(args: &[Arc<Object>]) -> Result<Arc<Object>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = args[0].as_ref();

    match arg {
        Object::Array(array) => {
            let elements = &array.read().unwrap().array;

            if elements.is_empty() {
                return Ok(Arc::new(Object::null()));
            }

            let new_elements = elements.get(1..).unwrap();
            let new_array = Object::arc_array(new_elements);
            Ok(Arc::new(new_array))
        }
        _ => Err(anyhow!("{arg:?} is not supported by push.")),
    }
}

pub fn push(args: &[Arc<Object>]) -> Result<Arc<Object>> {
    ensure!(
        args.len() == 2,
        "wrong number of arguments. got: {}, expected: 2",
        args.len()
    );

    let first_arg = &*args[0];
    let element = &*args[1];

    match first_arg {
        Object::Array(array) => {
            array.write().unwrap().array.push(Arc::new(element.clone()));
            Ok(Arc::new(Object::null()))
        }
        _ => Err(anyhow!("{first_arg:?} is not supported by push.")),
    }
}

pub fn puts(args: &[Arc<Object>]) -> Result<Arc<Object>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = &*args[0];

    println!("{}", arg);

    Ok(create_null())
}
