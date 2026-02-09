const INTEGER_OBJ: &str = "INTEGER";
const BOOL_OBJ: &str = "BOOL";
const NULL_OBJ: &str = "NULL";

#[derive(Debug, Clone)]
pub enum Object {
    Integer(Integer),
    Bool(Bool),
    Null(Null),
}

impl Object {
    fn get_type(&self) -> &'static str {
        match self {
            Self::Integer(_) => INTEGER_OBJ,
            Self::Bool(_) => BOOL_OBJ,
            Self::Null(_) => NULL_OBJ,
        }
    }

    fn inspect() -> String {
        todo!()
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

// Null
#[derive(Debug, Clone)]
pub struct Null {}
