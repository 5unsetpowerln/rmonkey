use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, LazyLock, Mutex, RwLock};

pub const GLOBAL_SCOPE: &str = "GLOBAL";
pub const LOCAL_SCOPE: &str = "LOCAL";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol {
    pub name: String,
    pub scope: String,
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

#[derive(Debug, Clone)]
pub struct SymbolTable {
    outer: Option<Arc<RwLock<SymbolTable>>>,
    store: HashMap<String, Symbol>,
    def_count: usize,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            outer: None,
            store: HashMap::new(),
            def_count: 0,
        }
    }

    pub fn new_enclosed(outer: Arc<RwLock<SymbolTable>>) -> Self {
        Self {
            outer: Some(outer),
            store: HashMap::new(),
            def_count: 0,
        }
    }

    pub fn define(&mut self, name: &str) -> Symbol {
        let symbol = if self.outer.is_some() {
            Symbol::new(name, LOCAL_SCOPE, self.def_count)
        } else {
            Symbol::new(name, GLOBAL_SCOPE, self.def_count)
        };

        self.store.insert(name.to_string(), symbol.clone());
        self.def_count += 1;
        symbol
    }

    pub fn resolve(&self, name: &str) -> Option<Symbol> {
        if let Some(resolved) = self.store.get(name) {
            return Some(resolved.clone());
        }

        if let Some(outer) = self.outer.as_ref() {
            return outer.read().unwrap().resolve(name);
        }

        None
    }

    pub fn outer(&self) -> Option<SymbolTable> {
        self.outer.as_ref().map(|x| x.read().unwrap().clone())
    }

    pub fn def_count(&self) -> usize {
        self.def_count
    }
}

impl PartialEq for SymbolTable {
    fn eq(&self, other: &Self) -> bool {
        if self.def_count != other.def_count || self.store != other.store {
            return false;
        }

        match (&self.outer, &other.outer) {
            (None, None) => true,
            (Some(a), Some(b)) => {
                if Arc::ptr_eq(&a, &b) {
                    return true;
                }

                let a = a.read().unwrap();
                let b = b.read().unwrap();

                a.eq(&*b)
            }
            _ => false,
        }
    }
}

mod test {
    use std::collections::HashMap;
    use std::sync::{Arc, RwLock};

    use super::{GLOBAL_SCOPE, LOCAL_SCOPE, Symbol, SymbolTable};

    #[test]
    fn test_define() {
        let mut global = Arc::new(RwLock::new(SymbolTable::new()));
        let mut first_local = Arc::new(RwLock::new(SymbolTable::new_enclosed(global.clone())));
        let mut second_local =
            Arc::new(RwLock::new(SymbolTable::new_enclosed(first_local.clone())));

        let a = global.write().unwrap().define("a");
        let b = global.write().unwrap().define("b");
        let c = first_local.write().unwrap().define("c");
        let d = first_local.write().unwrap().define("d");
        let e = second_local.write().unwrap().define("e");
        let f = second_local.write().unwrap().define("f");

        let tests = [
            (a, Symbol::new("a", GLOBAL_SCOPE, 0)),
            (b, Symbol::new("b", GLOBAL_SCOPE, 1)),
            (c, Symbol::new("c", LOCAL_SCOPE, 0)),
            (d, Symbol::new("d", LOCAL_SCOPE, 1)),
            (e, Symbol::new("e", LOCAL_SCOPE, 0)),
            (f, Symbol::new("f", LOCAL_SCOPE, 1)),
        ];

        for test in tests.iter() {
            if test.0 != test.1 {
                panic!("expected: {:?}, got: {:?}", &test.0, &test.1);
            }
        }
    }

    #[test]
    fn test_resolve() {
        let mut global = SymbolTable::new();
        global.define("a");
        global.define("b");

        let expected = [
            Symbol::new("a", GLOBAL_SCOPE, 0),
            Symbol::new("b", GLOBAL_SCOPE, 1),
        ];

        for symbol in expected.iter() {
            if let Some(s) = global.resolve(&symbol.name) {
                if s != *symbol {
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

    #[test]
    fn test_resolve_local() {
        let mut global = SymbolTable::new();

        global.define("a");
        global.define("b");

        let mut local = SymbolTable::new_enclosed(Arc::new(RwLock::new(global)));

        local.define("c");
        local.define("d");

        let expected = vec![
            Symbol::new("a", GLOBAL_SCOPE, 0),
            Symbol::new("b", GLOBAL_SCOPE, 1),
            Symbol::new("c", LOCAL_SCOPE, 0),
            Symbol::new("d", LOCAL_SCOPE, 1),
        ];

        for (i, symbol) in expected.iter().enumerate() {
            let resolved_symbol = local.resolve(&symbol.name).unwrap_or_else(|| {
                panic!("`{}` is not resolvable", symbol.name);
            });

            if *symbol != resolved_symbol {
                panic!("expected: {:?}, got: {:?}", symbol, resolved_symbol);
            }
        }
    }

    #[test]
    fn test_resolve_nested_local() {
        let mut global = Arc::new(RwLock::new(SymbolTable::new()));

        global.write().unwrap().define("a");
        global.write().unwrap().define("b");

        let first_local = {
            let mut local = SymbolTable::new_enclosed(global.clone());
            local.define("c");
            local.define("d");
            Arc::new(RwLock::new(local))
        };

        let second_local = {
            let mut local = SymbolTable::new_enclosed(first_local.clone());
            local.define("e");
            local.define("f");
            Arc::new(RwLock::new(local))
        };

        let tests = [
            (
                first_local,
                vec![
                    Symbol::new("a", GLOBAL_SCOPE, 0),
                    Symbol::new("b", GLOBAL_SCOPE, 1),
                    Symbol::new("c", LOCAL_SCOPE, 0),
                    Symbol::new("d", LOCAL_SCOPE, 1),
                ],
            ),
            (
                second_local,
                vec![
                    Symbol::new("a", GLOBAL_SCOPE, 0),
                    Symbol::new("b", GLOBAL_SCOPE, 1),
                    Symbol::new("e", LOCAL_SCOPE, 0),
                    Symbol::new("f", LOCAL_SCOPE, 1),
                ],
            ),
        ];

        for (i, (symbol_table, symbols)) in tests.iter().enumerate() {
            for (j, symbol) in symbols.iter().enumerate() {
                let st = symbol_table.read().unwrap();
                let resolved_symbol = st.resolve(&symbol.name).unwrap_or_else(|| {
                    panic!("`{}` is not resolvable.", &symbol.name);
                });

                if *symbol != resolved_symbol {
                    panic!("expected: {:?}, got: {:?}", symbol, resolved_symbol);
                }
            }
        }
    }
}
