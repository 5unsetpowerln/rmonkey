use std::ascii;
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::fmt::Display;
use std::rc::Rc;

use anyhow::{Result, bail, ensure};

use crate::ast::{self, BoolLiteral, FunctionLiteral, NodeInterface};

pub trait ObjectInterface: Display {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Object {
    Integer(Rc<Integer>),
    Bool(Rc<Bool>),
    Null(Rc<Null>),
    Function(Rc<Function>),
    ReturnValue(Rc<ReturnValue>),
    String(Rc<StringObject>),
}

impl Object {
    pub fn as_interface(&self) -> Rc<dyn ObjectInterface> {
        match self {
            Object::Bool(x) => x.clone(),
            Object::Integer(x) => x.clone(),
            Object::Null(x) => x.clone(),
            Object::ReturnValue(x) => x.clone(),
            Object::Function(x) => x.clone(),
            Object::String(x) => x.clone(),
        }
    }

    pub fn int(val: i64) -> Self {
        Self::Integer(Rc::new(Integer::new(val)))
    }

    pub fn bool(value: bool) -> Self {
        Self::Bool(Rc::new(Bool::new(value)))
    }

    pub fn null() -> Self {
        Self::Null(Rc::new(Null::new()))
    }

    pub fn str(value: &[ascii::Char]) -> Self {
        Self::String(Rc::new(StringObject::new(value)))
    }

    pub fn from_func_litereal(literal: &FunctionLiteral, env: Rc<RefCell<Environment>>) -> Self {
        Self::Function(Rc::new(Function::new(&literal.params, &literal.body, env)))
    }

    pub fn ret_val(val: Rc<Object>) -> Self {
        Self::ReturnValue(Rc::new(ReturnValue::new(val)))
    }

    pub fn is_returned(&self) -> bool {
        matches!(self, Self::ReturnValue(_))
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_interface())
    }
}

// Integer
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Integer {
    pub value: i64,
}

impl Integer {
    pub fn new(value: i64) -> Self {
        Self { value }
    }
}

impl ObjectInterface for Integer {}

impl Display for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

// Bool
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Bool {
    pub value: bool,
}

impl Bool {
    pub const fn new(value: bool) -> Self {
        Self { value }
    }
}

impl ObjectInterface for Bool {}

impl Display for Bool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

// Null
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Null {}

impl Null {
    pub const fn new() -> Self {
        Self {}
    }
}

impl Display for Null {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "null")
    }
}

impl ObjectInterface for Null {}

// String
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringObject {
    pub value: Vec<ascii::Char>,
}

impl StringObject {
    pub fn new(value: &[ascii::Char]) -> Self {
        Self {
            value: value.to_vec(),
        }
    }
}

impl Display for StringObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value.as_str())
    }
}

impl ObjectInterface for StringObject {}

// ReturnValue
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnValue {
    pub value: Rc<Object>,
}

impl ReturnValue {
    pub fn new(value: Rc<Object>) -> Self {
        Self { value }
    }
}

impl ObjectInterface for ReturnValue {}

impl Display for ReturnValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ret ({})", self.value)
    }
}

// Function
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub params: Vec<ast::Identifier>,
    pub body: ast::BlockStatement,
    pub parent_env: Rc<RefCell<Environment>>,
}

impl Function {
    pub fn new(
        params: &[ast::Identifier],
        body: &ast::BlockStatement,
        parent_env: Rc<RefCell<Environment>>,
    ) -> Self {
        Self {
            params: params.to_vec(),
            body: body.clone(),
            parent_env,
        }
    }

    pub fn create_function_env(&self, args: &[Rc<Object>]) -> Result<Rc<RefCell<Environment>>> {
        let mut env = Environment::new(Some(self.parent_env.clone()));

        ensure!(
            args.len() == self.params.len(),
            "number of params and number of actual arguments are not equal."
        );

        for (i, param) in self.params.iter().enumerate() {
            env.set(param.value.as_str(), args[i].clone());
        }

        Ok(Rc::new(RefCell::new(env)))
    }
}

impl ObjectInterface for Function {}

impl Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buffer = String::new();

        buffer.push_str("fn(");

        for (i, param) in self.params.iter().enumerate() {
            buffer.push_str(param.value.as_str());

            if i < self.params.len() - 1 {
                buffer.push_str(", ")
            }
        }

        buffer.push_str(") {\n");
        buffer.push_str(self.body.string().as_str());
        buffer.push_str("\n}");

        write!(f, "{buffer}")
    }
}

// helper constants
pub fn create_true() -> Rc<Object> {
    Rc::new(Object::bool(true))
}

pub fn create_false() -> Rc<Object> {
    Rc::new(Object::bool(false))
}

pub fn create_null() -> Rc<Object> {
    Rc::new(Object::null())
}

// environment
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Environment {
    store: HashMap<String, Rc<Object>>,
    outer: Option<Rc<RefCell<Environment>>>,
}

impl Environment {
    pub fn new(outer: Option<Rc<RefCell<Environment>>>) -> Self {
        Self {
            store: HashMap::new(),
            outer,
        }
    }

    pub fn get(&self, name: &str) -> Option<Rc<Object>> {
        match self.store.get(name) {
            Some(x) => Some(x.clone()),
            None => self.outer.as_ref()?.borrow().get(name),
        }
    }

    pub fn set(&mut self, name: &str, val: Rc<Object>) {
        self.store.insert(name.to_string(), val);
    }
}
