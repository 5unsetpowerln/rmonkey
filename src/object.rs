use std::ascii;
use std::collections::HashMap;
use std::fmt::Display;
use std::hash::Hash;
use std::sync::{Arc, RwLock};

use anyhow::{Result, anyhow, bail, ensure};

use crate::ast::{self, FunctionLiteral};
use crate::eval::EvalError;

pub trait ObjectInterface: Display + Send {
    fn get_name(&self) -> String;
}

#[derive(Debug, Clone)]
pub enum Object {
    Integer(Arc<RwLock<IntegerObject>>),
    Bool(Arc<RwLock<BoolObject>>),
    Null(Arc<RwLock<Null>>),
    Function(Arc<RwLock<Function>>),
    ReturnValue(Arc<RwLock<ReturnValue>>),
    String(Arc<RwLock<StringObject>>),
    Builtin(Arc<RwLock<Builtin>>),
    Array(Arc<RwLock<Array>>),
    Hash(Arc<RwLock<HashObject>>),
}

impl PartialEq for Object {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Object::Integer(a), Object::Integer(b)) => *a.read().unwrap() == *b.read().unwrap(),
            (Object::Bool(a), Object::Bool(b)) => *a.read().unwrap() == *b.read().unwrap(),
            (Object::Null(_), Object::Null(_)) => true,
            (Object::Function(a), Object::Function(b)) => *a.read().unwrap() == *b.read().unwrap(),
            (Object::ReturnValue(a), Object::ReturnValue(b)) => {
                *a.read().unwrap() == *b.read().unwrap()
            }
            (Object::String(a), Object::String(b)) => *a.read().unwrap() == *b.read().unwrap(),
            (Object::Builtin(a), Object::Builtin(b)) => *a.read().unwrap() == *b.read().unwrap(),
            (Object::Array(a), Object::Array(b)) => *a.read().unwrap() == *b.read().unwrap(),
            (Object::Hash(a), Object::Hash(b)) => *a.read().unwrap() == *b.read().unwrap(),
            _ => false,
        }
    }
}

impl Eq for Object {}

impl Object {
    pub fn as_interface(&self) -> Arc<RwLock<dyn ObjectInterface>> {
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
        Self::Integer(Arc::new(RwLock::new(IntegerObject::new(val))))
    }

    pub fn bool(value: bool) -> Self {
        Self::Bool(Arc::new(RwLock::new(BoolObject::new(value))))
    }

    pub fn null() -> Self {
        Self::Null(Arc::new(RwLock::new(Null::new())))
    }

    pub fn str(value: &str) -> Self {
        Self::String(Arc::new(RwLock::new(StringObject::new(value))))
    }

    pub fn array(array: &[Object]) -> Self {
        let arc_array = array
            .iter()
            .map(|element| Arc::new(element.clone()))
            .collect::<Vec<Arc<Object>>>();
        Self::Array(Arc::new(RwLock::new(Array::new(&arc_array))))
    }

    pub fn arc_array(array: &[Arc<Object>]) -> Self {
        Self::Array(Arc::new(RwLock::new(Array::new(array))))
    }

    pub fn builtin(func: BuiltinFunction) -> Self {
        Self::Builtin(Arc::new(RwLock::new(Builtin::new(func))))
    }

    pub fn from_func_litereal(literal: &FunctionLiteral, env: Arc<RwLock<Environment>>) -> Self {
        Self::Function(Arc::new(RwLock::new(Function::new(
            &literal.params,
            &literal.body,
            env,
        ))))
    }

    pub fn ret_val(val: Arc<Object>) -> Self {
        Self::ReturnValue(Arc::new(RwLock::new(ReturnValue::new(val))))
    }

    pub fn is_returned(&self) -> bool {
        matches!(self, Self::ReturnValue(_))
    }

    pub fn is_truthy(&self) -> bool {
        match self {
            Object::Bool(b) => b.read().unwrap().value,
            Object::Null(_) => false,
            _ => true,
        }
    }
}

impl ObjectInterface for Object {
    fn get_name(&self) -> String {
        self.as_interface().read().unwrap().get_name()
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_interface().read().unwrap())
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

impl ObjectInterface for IntegerObject {
    fn get_name(&self) -> String {
        "int".to_string()
    }
}

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

impl ObjectInterface for BoolObject {
    fn get_name(&self) -> String {
        "bool".to_string()
    }
}

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

impl ObjectInterface for Null {
    fn get_name(&self) -> String {
        "null".to_string()
    }
}

// String
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StringObject {
    pub value: String,
}

impl StringObject {
    pub fn new(value: &str) -> Self {
        Self {
            value: value.to_string(),
        }
    }
}

impl Display for StringObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value.as_str())
    }
}

impl ObjectInterface for StringObject {
    fn get_name(&self) -> String {
        "string".to_string()
    }
}

// ReturnValue
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnValue {
    pub value: Arc<Object>,
}

impl ReturnValue {
    pub fn new(value: Arc<Object>) -> Self {
        Self { value }
    }
}

impl ObjectInterface for ReturnValue {
    fn get_name(&self) -> String {
        "return value".to_string()
    }
}

impl Display for ReturnValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ret ({})", self.value)
    }
}

// Function
#[derive(Debug, Clone)]
pub struct Function {
    pub params: Vec<ast::Identifier>,
    pub body: ast::BlockStatement,
    pub parent_env: Arc<RwLock<Environment>>,
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        self.params == other.params
            && self.body == other.body
            && *self.parent_env.read().unwrap() == *other.parent_env.read().unwrap()
    }
}

impl Eq for Function {}

impl Function {
    pub fn new(
        params: &[ast::Identifier],
        body: &ast::BlockStatement,
        parent_env: Arc<RwLock<Environment>>,
    ) -> Self {
        Self {
            params: params.to_vec(),
            body: body.clone(),
            parent_env,
        }
    }

    pub fn create_function_env(&self, args: &[Arc<Object>]) -> Result<Arc<RwLock<Environment>>> {
        let mut env = Environment::new(Some(self.parent_env.clone()));

        ensure!(
            args.len() == self.params.len(),
            "number of params and number of actual arguments are not equal."
        );

        for (i, param) in self.params.iter().enumerate() {
            env.set(param.value.as_str(), args[i].clone());
        }

        Ok(Arc::new(RwLock::new(env)))
    }
}

impl ObjectInterface for Function {
    fn get_name(&self) -> String {
        "function".to_string()
    }
}

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
        buffer.push_str(self.body.to_string().as_str());
        buffer.push_str("\n}");

        write!(f, "{buffer}")
    }
}

// Array
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Array {
    pub array: Vec<Arc<Object>>,
}

impl Array {
    pub fn new(array: &[Arc<Object>]) -> Self {
        Self {
            array: array.to_vec(),
        }
    }
}

impl ObjectInterface for Array {
    fn get_name(&self) -> String {
        "array".to_string()
    }
}

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
#[derive(Debug, Clone)]
pub enum HashKeyObject {
    String(Arc<RwLock<StringObject>>),
    Integer(Arc<RwLock<IntegerObject>>),
    Bool(Arc<RwLock<BoolObject>>),
}

impl PartialEq for HashKeyObject {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::String(a), Self::String(b)) => *a.read().unwrap() == *b.read().unwrap(),
            (Self::Integer(a), Self::Integer(b)) => *a.read().unwrap() == *b.read().unwrap(),
            (Self::Bool(a), Self::Bool(b)) => *a.read().unwrap() == *b.read().unwrap(),
            _ => false,
        }
    }
}

impl Eq for HashKeyObject {}

impl HashKeyObject {
    pub fn from_object(object: Arc<Object>) -> Result<Self> {
        let s = match &*object {
            Object::String(x) => Self::String(x.clone()),
            Object::Integer(x) => Self::Integer(x.clone()),
            Object::Bool(x) => Self::Bool(x.clone()),
            _ => {
                bail!(EvalError::NotHashable {
                    got: object.get_name()
                })
            }
        };

        Ok(s)
    }

    pub fn str(value: &str) -> Self {
        Self::String(Arc::new(RwLock::new(StringObject::new(value))))
    }

    pub fn int(value: i64) -> Self {
        Self::Integer(Arc::new(RwLock::new(IntegerObject::new(value))))
    }

    pub fn bool(value: bool) -> Self {
        Self::Bool(Arc::new(RwLock::new(BoolObject::new(value))))
    }

    fn as_interface(&self) -> Arc<RwLock<dyn ObjectInterface>> {
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
            Self::String(x) => x.read().unwrap().hash(state),
            Self::Integer(x) => x.read().unwrap().hash(state),
            Self::Bool(x) => x.read().unwrap().hash(state),
        }
    }
}

impl Display for HashKeyObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_interface().read().unwrap())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HashObject {
    pub pairs: HashMap<HashKeyObject, Arc<Object>>,
}

impl HashObject {
    pub fn new(pairs: HashMap<HashKeyObject, Arc<Object>>) -> Self {
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

impl ObjectInterface for HashObject {
    fn get_name(&self) -> String {
        "hash".to_string()
    }
}

// Builtin
pub type BuiltinFunction = fn(&[Arc<Object>]) -> Result<Option<Arc<Object>>>;

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

impl ObjectInterface for Builtin {
    fn get_name(&self) -> String {
        "builtin".to_string()
    }
}

// helper constants
pub fn create_true() -> Arc<Object> {
    Arc::new(Object::bool(true))
}

pub fn create_false() -> Arc<Object> {
    Arc::new(Object::bool(false))
}

pub fn create_null() -> Arc<Object> {
    Arc::new(Object::null())
}

// environment
#[derive(Debug, Clone)]
pub struct Environment {
    store: HashMap<String, Arc<Object>>,
    outer: Option<Arc<RwLock<Environment>>>,
}

impl PartialEq for Environment {
    fn eq(&self, other: &Self) -> bool {
        if self.store != other.store {
            return false;
        }
        match (&self.outer, &other.outer) {
            (None, None) => true,
            (Some(a), Some(b)) => *a.read().unwrap() == *b.read().unwrap(),
            _ => false,
        }
    }
}

impl Eq for Environment {}

impl Environment {
    pub fn new(outer: Option<Arc<RwLock<Environment>>>) -> Self {
        Self {
            store: HashMap::new(),
            outer,
        }
    }

    pub fn get(&self, name: &str) -> Option<Arc<Object>> {
        match self.store.get(name) {
            Some(x) => Some(x.clone()),
            None => self.outer.as_ref()?.read().unwrap().get(name),
        }
    }

    pub fn set(&mut self, name: &str, val: Arc<Object>) {
        self.store.insert(name.to_string(), val);
    }
}
