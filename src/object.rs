use std::fmt::Display;

pub trait ObjectInterface: Display {}

#[derive(Debug, Clone)]
pub enum Object {
    Integer(Integer),
    Bool(Bool),
    Null(Null),
}

impl Object {
    pub fn as_interface(&self) -> &dyn ObjectInterface {
        match self {
            Object::Bool(x) => x,
            Object::Integer(x) => x,
            Object::Null(x) => x,
        }
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_interface())
    }
}

// Integer
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
pub struct Bool {
    pub value: bool,
}

impl Bool {
    pub fn new(value: bool) -> Self {
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
#[derive(Debug, Clone)]
pub struct Null {}

impl Display for Null {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "null")
    }
}

impl ObjectInterface for Null {}
