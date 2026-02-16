use std::rc::Rc;

use anyhow::{Result, anyhow, ensure};

use crate::object::{Object, create_null};

pub fn len(args: &[Rc<Object>]) -> Result<Rc<Object>> {
    ensure!(
        args.len() == 1,
        "wrong number of arguments. got: {}, expected: 1",
        args.len()
    );

    let arg = &*args[0];

    match arg {
        Object::String(s) => Ok(Rc::new(Object::int(s.value.len() as i64))),
        _ => Err(anyhow!("{arg:?} is not supported by len.")),
    }
}
