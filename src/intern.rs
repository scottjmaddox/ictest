use once_cell::sync::Lazy;
use std::collections::HashSet;
use std::sync::RwLock;

static INTERNED: Lazy<RwLock<HashSet<&'static str>>> = Lazy::new(|| RwLock::new(HashSet::new()));

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IStr(&'static str);

impl IStr {
    #[allow(dead_code)]
    pub fn as_ptr(&self) -> *const str {
        self.0
    }
}

impl std::fmt::Display for IStr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub trait Intern {
    fn intern(&self) -> IStr;
}

impl From<String> for IStr {
    fn from(s: String) -> IStr {
        s.as_str().intern()
    }
}

impl From<&'static str> for IStr {
    fn from(s: &'static str) -> IStr {
        s.intern_static()
    }
}

pub trait InternStatic {
    fn intern_static(&self) -> IStr;
}

impl<S: AsRef<str>> Intern for S {
    fn intern(&self) -> IStr {
        let s = self.as_ref();
        if let Some(s) = INTERNED.read().unwrap().get(s) {
            return IStr(s);
        }
        let s = Box::leak(s.to_string().into_boxed_str());
        INTERNED.write().unwrap().insert(s);
        IStr(s)
    }
}

impl InternStatic for &'static str {
    fn intern_static(&self) -> IStr {
        if let Some(s) = INTERNED.read().unwrap().get(self) {
            return IStr(s);
        }
        INTERNED.write().unwrap().insert(self);
        IStr(self)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_intern() {
        let s1 = "test_intern".to_owned();
        let s2 = "test_intern".to_owned();
        assert_eq!(s1.intern().as_ptr(), s2.intern().as_ptr());
    }

    #[test]
    fn test_intern_static() {
        let s1 = "test_intern_static";
        let s2 = "test_intern_static";
        assert_eq!(s1.intern_static().as_ptr(), s2.intern_static().as_ptr());
    }
}
