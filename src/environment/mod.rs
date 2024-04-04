use crate::object;
use std::collections::HashMap;
use std::rc::Rc;

pub struct Environment {
    store: HashMap<String, Rc<object::Object>>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            store: HashMap::new(),
        }
    }

    pub fn get(&self, name: &str) -> Option<Rc<object::Object>> {
        self.store.get(name).cloned()
    }

    pub fn set(&mut self, name: String, value: Rc<object::Object>) {
        self.store.insert(name, value);
    }
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}
