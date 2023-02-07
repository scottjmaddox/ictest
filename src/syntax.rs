use crate::intern::IStr;
use std::fmt;

pub type Label = u64;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// Variable, e.g. `x`
    Var(IStr),
    /// Lambda, e.g. `(λx body)`
    Lam(IStr, Box<Term>),
    /// Application, e.g. `(f arg)`
    App(Box<Term>, Box<Term>),
    /// Superposition, e.g. `#0{x y}`
    Sup(Label, Box<Term>, Box<Term>),
    /// Duplication, e.g. `dup #0{x y} = z; body`
    Dup(Label, IStr, IStr, Box<Term>, Box<Term>),
    /// Let, e.g. `let x = expr; body`
    Let(IStr, Box<Term>, Box<Term>),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Var(v) => write!(f, "{}", v),
            Term::Lam(x, body) => write!(f, "(λ{} {})", x, body),
            Term::App(fun, arg) => write!(f, "({} {})", fun, arg),
            Term::Sup(label, left, right) => write!(f, "#{}{{{} {}}}", label, left, right),
            Term::Dup(label, x, y, dup, body) => {
                write!(f, "(dup #{}{{{} {}}} = {}; {})", label, x, y, dup, body)
            }
            Term::Let(x, expr, body) => write!(f, "(let {} = {}; {})", x, expr, body),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::intern::InternStatic;

    #[test]
    fn test_display_term() {
        let x = "x".intern_static();
        let y = "y".intern_static();
        let z = "z".intern_static();
        let f = "f".intern_static();
        let arg = "arg".intern_static();
        let body = "body".intern_static();
        let expr = "expr".intern_static();

        let test_cases = &[
            (Term::Var(x), "x"),
            (Term::Lam(x, Box::new(Term::Var(y))), "(λx y)"),
            (
                Term::App(Box::new(Term::Var(f)), Box::new(Term::Var(arg))),
                "(f arg)",
            ),
            (
                Term::Sup(0, Box::new(Term::Var(x)), Box::new(Term::Var(y))),
                "#0{x y}",
            ),
            (
                Term::Dup(0, x, y, Box::new(Term::Var(z)), Box::new(Term::Var(body))),
                "(dup #0{x y} = z; body)",
            ),
            (
                Term::Let(x, Box::new(Term::Var(expr)), Box::new(Term::Var(body))),
                "(let x = expr; body)",
            ),
        ];
        for (term, expected) in test_cases {
            assert_eq!(term.to_string(), *expected);
        }
    }
}
