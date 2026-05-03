use std::sync::Arc;

use anyhow::{Context, Result, anyhow, ensure};

use crate::object::{Object, create_null};

pub fn len(args: &[Arc<Object>]) -> Result<Option<Arc<Object>>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = &*args[0];

    match arg {
        Object::String(s) => Ok(Some(Arc::new(Object::int(
            s.read().unwrap().value.len() as i64
        )))),
        Object::Array(a) => Ok(Some(Arc::new(Object::int(
            a.read().unwrap().array.len() as i64
        )))),
        _ => Err(anyhow!("{arg:?} is not supported by len.")),
    }
}

pub fn first(args: &[Arc<Object>]) -> Result<Option<Arc<Object>>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = &*args[0];

    match arg {
        Object::Array(array) => Ok(Some(
            array
                .read()
                .unwrap()
                .array
                .first()
                .context("the array is empty.")?
                .clone(),
        )),
        _ => Err(anyhow!("{arg:?} is not supported by first.")),
    }
}

pub fn last(args: &[Arc<Object>]) -> Result<Option<Arc<Object>>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = &*args[0];

    match arg {
        Object::Array(array) => Ok(Some(
            array
                .read()
                .unwrap()
                .array
                .last()
                .context("the array is empty.")?
                .clone(),
        )),
        _ => Err(anyhow!("{arg:?} is not supported by last.")),
    }
}

pub fn push(args: &[Arc<Object>]) -> Result<Option<Arc<Object>>> {
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
            Ok(Some(Arc::new(Object::null())))
        }
        _ => Err(anyhow!("{first_arg:?} is not supported by push.")),
    }
}

pub fn puts(args: &[Arc<Object>]) -> Result<Option<Arc<Object>>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = &*args[0];

    println!("{}", arg);

    Ok(Some(create_null()))
}
