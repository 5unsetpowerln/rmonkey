use std::collections::{BTreeMap, HashMap};
use std::fmt::Display;

pub trait ObjectInterface: Display {}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Object {
    Integer(Integer),
    Bool(Bool),
    Null(Null),
    ReturnValue(ReturnValue),
}

impl Object {
    pub fn as_interface(&self) -> &dyn ObjectInterface {
        match self {
            Object::Bool(x) => x,
            Object::Integer(x) => x,
            Object::Null(x) => x,
            Object::ReturnValue(x) => x,
        }
    }

    pub fn int(val: i64) -> Self {
        Self::Integer(Integer::new(val))
    }

    pub fn bool(val: bool) -> Self {
        Self::Bool(Bool::new(val))
    }

    pub fn null() -> Self {
        Self::Null(Null::new())
    }

    pub fn ret_val(val: Object) -> Self {
        Self::ReturnValue(ReturnValue::new(val))
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

// ReturnValue
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ReturnValue {
    pub value: Box<Object>,
}

impl ReturnValue {
    pub fn new(value: Object) -> Self {
        Self {
            value: Box::new(value),
        }
    }
}

impl ObjectInterface for ReturnValue {}

impl Display for ReturnValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ret ({})", self.value)
    }
}

// helper constants
pub const TRUE: Object = Object::Bool(Bool::new(true));
pub const FALSE: Object = Object::Bool(Bool::new(false));
pub const NULL: Object = Object::Null(Null::new());

// environment
#[derive(Debug)]
pub struct Environment {
    store: HashMap<String, Object>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
        }
    }

    pub fn get(&self, name: &str) -> Option<&Object> {
        self.store.get(name)
    }

    pub fn set(&mut self, name: &str, val: Object) {
        self.store.insert(name.to_string(), val);
    }
}
