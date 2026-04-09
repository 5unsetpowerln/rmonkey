use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

const GLOBAL_SCOPE: &str = "GLOBAL";
static DEF_COUNT: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol {
    pub name: String,
    scope: String,
    pub index: usize,
}

impl Symbol {
    pub fn new(name: &str, scope: &str, index: usize) -> Self {
        Self {
            name: name.to_string(),
            scope: scope.to_string(),
            index,
        }
    }
}

#[derive(Debug)]
pub struct SymbolTable {
    store: HashMap<String, Symbol>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
        }
    }

    pub fn define(&mut self, name: &str) -> Symbol {
        let symbol = Symbol::new(name, GLOBAL_SCOPE, DEF_COUNT.load(Ordering::SeqCst));
        self.store.insert(name.to_string(), symbol.clone());
        DEF_COUNT.fetch_add(1, Ordering::SeqCst);
        symbol
    }

    pub fn resolve(&self, name: &str) -> Option<&Symbol> {
        self.store.get(name)
    }
}

pub fn create_symbol_table() -> SymbolTable {
    SymbolTable::new()
}

pub unsafe fn reset_symbol_count() {
    DEF_COUNT.store(0, Ordering::SeqCst);
}

mod test {
    use std::collections::HashMap;

    use super::{GLOBAL_SCOPE, Symbol, create_symbol_table, reset_symbol_count};

    #[test]
    fn test_define() {
        unsafe {
            reset_symbol_count();
        }
        let mut expected = HashMap::new();
        expected.insert("a", Symbol::new("a", GLOBAL_SCOPE, 0));
        expected.insert("b", Symbol::new("b", GLOBAL_SCOPE, 1));

        let mut global = create_symbol_table();

        let a = global.define("a");

        if a != expected["a"] {
            panic!("expected: {:?}, got: {:?}", &expected["a"], a);
        }

        let b = global.define("b");

        if b != expected["b"] {
            panic!("expected: {:?}, got: {:?}", &expected["b"], b);
        }
    }

    #[test]
    fn test_resolve() {
        unsafe {
            reset_symbol_count();
        }
        let mut global = create_symbol_table();
        global.define("a");
        global.define("b");

        let expected = [
            Symbol::new("a", GLOBAL_SCOPE, 0),
            Symbol::new("b", GLOBAL_SCOPE, 1),
        ];

        for symbol in expected.iter() {
            if let Some(s) = global.resolve(&symbol.name) {
                if *s != *symbol {
                    panic!(
                        "expected `{}` to resolve to {:?}. got: {:?}",
                        &symbol.name, symbol, s
                    );
                }
            } else {
                panic!("name `{}` not resolvable.", &symbol.name);
            }
        }
    }
}
