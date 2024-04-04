use crate::object;
use std::collections::HashMap;

pub struct Environment {
    store: HashMap<String, object::Object>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            store: HashMap::new(),
        }
    }

    pub fn get(&self, name: &str) -> Option<&object::Object> {
        self.store.get(name)
    }

    pub fn set(&mut self, name: String, value: object::Object) {
        self.store.insert(name, value);
    }
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}
