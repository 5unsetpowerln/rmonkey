use std::ascii;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Display;
use std::hash::Hash;
use std::rc::Rc;

use anyhow::{Result, anyhow, bail, ensure};

use crate::ast::{self, ArrayLiteral, BoolLiteral, FunctionLiteral, NodeInterface};

pub trait ObjectInterface: Display {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Object {
    Integer(Rc<RefCell<IntegerObject>>),
    Bool(Rc<RefCell<BoolObject>>),
    Null(Rc<RefCell<Null>>),
    Function(Rc<RefCell<Function>>),
    ReturnValue(Rc<RefCell<ReturnValue>>),
    String(Rc<RefCell<StringObject>>),
    Builtin(Rc<RefCell<Builtin>>),
    Array(Rc<RefCell<Array>>),
    Hash(Rc<RefCell<HashObject>>),
}

impl Object {
    pub fn as_interface(&self) -> Rc<RefCell<dyn ObjectInterface>> {
        match self {
            Object::Bool(x) => x.clone(),
            Object::Integer(x) => x.clone(),
            Object::Null(x) => x.clone(),
            Object::ReturnValue(x) => x.clone(),
            Object::Function(x) => x.clone(),
            Object::String(x) => x.clone(),
            Object::Builtin(x) => x.clone(),
            Object::Array(x) => x.clone(),
            Object::Hash(x) => x.clone(),
        }
    }

    pub fn int(val: i64) -> Self {
        Self::Integer(Rc::new(RefCell::new(IntegerObject::new(val))))
    }

    pub fn bool(value: bool) -> Self {
        Self::Bool(Rc::new(RefCell::new(BoolObject::new(value))))
    }

    pub fn null() -> Self {
        Self::Null(Rc::new(RefCell::new(Null::new())))
    }

    pub fn str(value: &[ascii::Char]) -> Self {
        Self::String(Rc::new(RefCell::new(StringObject::new(value))))
    }

    pub fn builtin(func: BuiltinFunction) -> Self {
        Self::Builtin(Rc::new(RefCell::new(Builtin::new(func))))
    }

    pub fn from_func_litereal(literal: &FunctionLiteral, env: Rc<RefCell<Environment>>) -> Self {
        Self::Function(Rc::new(RefCell::new(Function::new(
            &literal.params,
            &literal.body,
            env,
        ))))
    }

    pub fn ret_val(val: Rc<Object>) -> Self {
        Self::ReturnValue(Rc::new(RefCell::new(ReturnValue::new(val))))
    }

    pub fn is_returned(&self) -> bool {
        matches!(self, Self::ReturnValue(_))
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_interface().borrow())
    }
}

// Integer
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IntegerObject {
    pub value: i64,
}

impl IntegerObject {
    pub fn new(value: i64) -> Self {
        Self { value }
    }
}

impl ObjectInterface for IntegerObject {}

impl Display for IntegerObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

// Bool
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BoolObject {
    pub value: bool,
}

impl BoolObject {
    pub const fn new(value: bool) -> Self {
        Self { value }
    }
}

impl ObjectInterface for BoolObject {}

impl Display for BoolObject {
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

// Array
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Array {
    pub array: Vec<Rc<Object>>,
}

impl Array {
    pub fn new(array: &[Rc<Object>]) -> Self {
        Self {
            array: array.to_vec(),
        }
    }
}

impl ObjectInterface for Array {}

impl Display for Array {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buffer = Vec::new();

        buffer.push(ascii::Char::LeftSquareBracket);

        for (i, obj) in self.array.iter().enumerate() {
            buffer.extend(format!("{obj}").as_ascii().unwrap());

            if i < self.array.len() - 1 {
                buffer.push(ascii::Char::Comma);
                buffer.push(ascii::Char::Space);
            }
        }

        buffer.push(ascii::Char::RightSquareBracket);

        write!(f, "{}", buffer.as_str())
    }
}

// Hash
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HashKeyObject {
    String(Rc<RefCell<StringObject>>),
    Integer(Rc<RefCell<IntegerObject>>),
    Bool(Rc<RefCell<BoolObject>>),
}

impl HashKeyObject {
    pub fn from_object(object: Rc<Object>) -> Result<Self> {
        let s = match &*object {
            Object::String(x) => Self::String(x.clone()),
            Object::Integer(x) => Self::Integer(x.clone()),
            Object::Bool(x) => Self::Bool(x.clone()),
            _ => {
                bail!(anyhow!("{:?} can't be key of hash.", object))
            }
        };

        Ok(s)
    }

    pub fn str(value: &str) -> Self {
        Self::String(Rc::new(RefCell::new(StringObject::new(
            value.as_ascii().unwrap(),
        ))))
    }

    pub fn int(value: i64) -> Self {
        Self::Integer(Rc::new(RefCell::new(IntegerObject::new(value))))
    }

    pub fn bool(value: bool) -> Self {
        Self::Bool(Rc::new(RefCell::new(BoolObject::new(value))))
    }

    fn as_interface(&self) -> Rc<RefCell<dyn ObjectInterface>> {
        match self {
            Self::String(x) => x.clone(),
            Self::Integer(x) => x.clone(),
            Self::Bool(x) => x.clone(),
        }
    }
}

impl Hash for HashKeyObject {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);

        match self {
            Self::String(x) => x.borrow().hash(state),
            Self::Integer(x) => x.borrow().hash(state),
            Self::Bool(x) => x.borrow().hash(state),
        }
    }
}

impl Display for HashKeyObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_interface().borrow())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HashObject {
    pub pairs: HashMap<HashKeyObject, Rc<Object>>,
}

impl HashObject {
    pub fn new(pairs: HashMap<HashKeyObject, Rc<Object>>) -> Self {
        Self { pairs }
    }
}

impl Display for HashObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buffer = String::new();

        buffer.push_str("{\n");

        for (k, v) in self.pairs.iter() {
            buffer.push_str(format!("\t{} : {},\n", k, v).as_str());
        }

        buffer.push('}');

        write!(f, "{buffer}")
    }
}

impl ObjectInterface for HashObject {}

// Builtin
pub type BuiltinFunction = fn(&[Rc<Object>]) -> Result<Rc<Object>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Builtin {
    pub func: BuiltinFunction,
}

impl Builtin {
    pub fn new(func: BuiltinFunction) -> Self {
        Self { func }
    }
}

impl Display for Builtin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "builtin function")
    }
}

impl ObjectInterface for Builtin {}

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
