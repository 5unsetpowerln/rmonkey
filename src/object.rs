use std::fmt::Display;

#[derive(Debug, Clone)]
pub enum Object {
    Integer(Integer),
    Bool(Bool),
    Null(Null),
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer(x) => write!(f, "{}", x),
            Self::Bool(x) => write!(f, "{}", x),
            _ => unimplemented!(),
        }
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

impl Display for Bool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

// Null
#[derive(Debug, Clone)]
pub struct Null {}
