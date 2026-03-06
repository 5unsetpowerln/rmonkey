use std::cell::RefCell;
use std::rc::Rc;

use anyhow::{Context, Result, anyhow, ensure};

use crate::object::{Object, create_null};

pub fn len(args: &[Rc<Object>]) -> Result<Option<Rc<Object>>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = &*args[0];

    match arg {
        Object::String(s) => Ok(Some(Rc::new(Object::int(s.borrow().value.len() as i64)))),
        Object::Array(a) => Ok(Some(Rc::new(Object::int(a.borrow().array.len() as i64)))),
        _ => Err(anyhow!("{arg:?} is not supported by len.")),
    }
}

pub fn first(args: &[Rc<Object>]) -> Result<Option<Rc<Object>>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = &*args[0];

    match arg {
        Object::Array(array) => Ok(Some(
            array
                .borrow()
                .array
                .first()
                .context("the array is empty.")?
                .clone(),
        )),
        _ => Err(anyhow!("{arg:?} is not supported by first.")),
    }
}

pub fn last(args: &[Rc<Object>]) -> Result<Option<Rc<Object>>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = &*args[0];

    match arg {
        Object::Array(array) => Ok(Some(
            array
                .borrow()
                .array
                .last()
                .context("the array is empty.")?
                .clone(),
        )),
        _ => Err(anyhow!("{arg:?} is not supported by last.")),
    }
}

pub fn push(args: &[Rc<Object>]) -> Result<Option<Rc<Object>>> {
    ensure!(
        args.len() == 2,
        "wrong number of arguments. got: {}, expected: 2",
        args.len()
    );

    let first_arg = &*args[0];
    let element = &*args[1];

    match first_arg {
        Object::Array(array) => {
            array.borrow_mut().array.push(Rc::new(element.clone()));
            Ok(Some(Rc::new(Object::null())))
        }
        _ => Err(anyhow!("{first_arg:?} is not supported by push.")),
    }
}

pub fn puts(args: &[Rc<Object>]) -> Result<Option<Rc<Object>>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = &*args[0];

    println!("{}", arg);

    Ok(Some(create_null()))
}
