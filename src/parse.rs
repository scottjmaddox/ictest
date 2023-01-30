// Modified from https://github.com/Kindelia/HVM/blob/master/src/language/syntax.rs
// Original licensed under the MIT License below.

// MIT License
//
// Copyright (c) 2023 Victor Maia
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use crate::intern::Intern;
use crate::parser;
use crate::syntax::{Label, Term};

pub fn parse_var(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
    parser::guard(
        Box::new(|state| {
            let (state, head) = parser::get_char(state)?;
            Ok((
                state,
                ('a'..='z').contains(&head) || head == '_' || head == '$',
            ))
        }),
        Box::new(|state| {
            let (state, name) = parser::name(state)?;
            Ok((state, Box::new(Term::Var(name.intern()))))
        }),
        state,
    )
}

pub fn parse_lam(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
    let parse_symbol =
        |x| parser::parser_or(&[parser::text_parser("λ"), parser::text_parser("@")], x);
    parser::guard(
        Box::new(parse_symbol),
        Box::new(move |state| {
            let (state, _) = parse_symbol(state)?;
            let (state, name) = parser::name(state)?;
            let (state, body) = parse_term(state)?;
            Ok((state, Box::new(Term::Lam(name.intern(), body))))
        }),
        state,
    )
}

pub fn parse_app(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
    return parser::guard(
        parser::text_parser("("),
        Box::new(|state| {
            parser::list(
                parser::text_parser("("),
                parser::text_parser(""),
                parser::text_parser(")"),
                Box::new(parse_term),
                Box::new(|args| {
                    if !args.is_empty() {
                        args.into_iter()
                            .reduce(|a, b| Box::new(Term::App(a, b)))
                            .unwrap()
                    } else {
                        todo!()
                    }
                }),
                state,
            )
        }),
        state,
    );
}

/// Parses a num right after the parsing cursor.
fn num_here(state: parser::State) -> parser::Answer<String> {
    let mut name: String = String::new();
    let mut state = state;
    while let Some(got) = parser::head(state) {
        if ('0'..='9').contains(&got) {
            name.push(got);
            state = parser::tail(state);
        } else {
            break;
        }
    }
    Ok((state, name))
}

/// Parses a label, e.g. `#0`, `#1`, `#2`, etc.
pub fn parse_label(state: parser::State) -> parser::Answer<Label> {
    let (state, _) = parser::consume("#", state)?;
    let (state, text) = num_here(state)?;
    let num = text.parse::<u64>().map_err(|_| "label out of range")?;
    Ok((state, num))
}

pub fn parse_sup(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
    parser::guard(
        parser::text_parser("#"),
        Box::new(move |state| {
            let (state, label) = parse_label(state)?;
            let (state, _) = parser::consume("{", state)?;
            let (state, val0) = parse_term(state)?;
            let (state, val1) = parse_term(state)?;
            let (state, _) = parser::consume("}", state)?;
            Ok((state, Box::new(Term::Sup(label, val0, val1))))
        }),
        state,
    )
}

pub fn parse_dup(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
    return parser::guard(
        parser::text_parser("dup "),
        Box::new(|state| {
            let (state, _) = parser::consume("dup ", state)?;
            let (state, label) = parse_label(state)?;
            let (state, _) = parser::consume("{", state)?;
            let (state, nam0) = parser::name1(state)?;
            let (state, nam1) = parser::name1(state)?;
            let (state, _) = parser::consume("}", state)?;
            let (state, _) = parser::consume("=", state)?;
            let (state, expr) = parse_term(state)?;
            let (state, _) = parser::text(";", state)?;
            let (state, body) = parse_term(state)?;
            Ok((
                state,
                Box::new(Term::Dup(label, nam0.intern(), nam1.intern(), expr, body)),
            ))
        }),
        state,
    );
}

pub fn parse_let(state: parser::State) -> parser::Answer<Option<Box<Term>>> {
    return parser::guard(
        parser::text_parser("let "),
        Box::new(|state| {
            let (state, _) = parser::consume("let ", state)?;
            let (state, name) = parser::name1(state)?;
            let (state, _) = parser::consume("=", state)?;
            let (state, expr) = parse_term(state)?;
            let (state, _) = parser::text(";", state)?;
            let (state, body) = parse_term(state)?;
            Ok((state, Box::new(Term::Let(name.intern(), expr, body))))
        }),
        state,
    );
}

pub fn parse_term(state: parser::State) -> parser::Answer<Box<Term>> {
    parser::grammar(
        "Term",
        &[
            Box::new(parse_let),
            Box::new(parse_dup),
            Box::new(parse_lam),
            Box::new(parse_app),
            Box::new(parse_sup),
            Box::new(parse_var),
            Box::new(|state| Ok((state, None))),
        ],
        state,
    )
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::intern::{IStr, InternStatic};
    use proptest::prelude::*;

    #[test]
    fn test_parse_term() {
        let x = "x".intern_static();
        let y = "y".intern_static();
        let z = "z".intern_static();
        let x0 = "x0".intern_static();
        let x1 = "x1".intern_static();
        let test_cases = &[
            (
                "λx λy x",
                Box::new(Term::Lam(x, Box::new(Term::Lam(y, Box::new(Term::Var(x)))))),
            ),
            (
                "λx dup #0{x0 x1} = x; #0{x0 x1}",
                Box::new(Term::Lam(
                    x,
                    Box::new(Term::Dup(
                        0,
                        x0,
                        x1,
                        Box::new(Term::Var(x)),
                        Box::new(Term::Sup(
                            0,
                            Box::new(Term::Var(x0)),
                            Box::new(Term::Var(x1)),
                        )),
                    )),
                )),
            ),
            (
                "let x = y;\nz",
                Box::new(Term::Let(x, Box::new(Term::Var(y)), Box::new(Term::Var(z)))),
            ),
        ];
        for (input, expected) in test_cases {
            let state = parser::State::new(input);
            let (state, term) = parse_term(state).unwrap();
            let (_, is_done) = parser::done(state).unwrap();
            assert!(is_done);
            assert_eq!(term, *expected);
        }
    }

    #[test]
    fn test_display_parse_term() {
        let x = "x".intern_static();
        let y = "y".intern_static();
        let z = "z".intern_static();
        let x0 = "x0".intern_static();
        let x1 = "x1".intern_static();
        let test_cases = &[
            Box::new(Term::Lam(x, Box::new(Term::Lam(y, Box::new(Term::Var(x)))))),
            Box::new(Term::Lam(
                x,
                Box::new(Term::Dup(
                    0,
                    x0,
                    x1,
                    Box::new(Term::Var(x)),
                    Box::new(Term::Sup(
                        0,
                        Box::new(Term::Var(x0)),
                        Box::new(Term::Var(x1)),
                    )),
                )),
            )),
            Box::new(Term::Let(x, Box::new(Term::Var(y)), Box::new(Term::Var(z)))),
        ];
        for term in test_cases {
            let input = format!("{}", term);
            let state = parser::State::new(&input);
            let (state, term2) = parse_term(state).unwrap();
            let (_, is_done) = parser::done(state).unwrap();
            assert!(is_done);
            assert_eq!(term, &term2);
        }
    }

    fn arb_var_name() -> impl Strategy<Value = IStr> {
        "[_a-z][_a-zA-Z0-9]*".prop_map(|s| s.into())
    }

    fn arb_label() -> impl Strategy<Value = Label> {
        prop::num::u64::ANY
    }

    fn arb_term() -> impl Strategy<Value = Term> {
        let leaf = arb_var_name().prop_map(|v| Term::Var(v));
        leaf.prop_recursive(8, 256, 5, |inner| {
            prop_oneof![
                (arb_var_name(), inner.clone()).prop_map(|(v, t)| Term::Lam(v, Box::new(t))),
                (inner.clone(), inner.clone())
                    .prop_map(|(f, arg)| Term::App(Box::new(f), Box::new(arg))),
                (arb_label(), inner.clone(), inner.clone()).prop_map(|(l, a, b)| Term::Sup(
                    l,
                    Box::new(a),
                    Box::new(b)
                )),
                (
                    arb_label(),
                    arb_var_name(),
                    arb_var_name(),
                    inner.clone(),
                    inner.clone()
                )
                    .prop_map(|(l, a, b, expr, cont)| Term::Dup(
                        l,
                        a,
                        b,
                        Box::new(expr),
                        Box::new(cont)
                    )),
                (arb_var_name(), inner.clone(), inner.clone()).prop_map(|(v, x, y)| Term::Let(
                    v,
                    Box::new(x),
                    Box::new(y)
                )),
            ]
        })
    }

    proptest! {
        #[test]
        fn test_display_parse_term_property(term in arb_term()) {
            let input = format!("{}", term);
            let state = parser::State::new(&input);
            let (state, term2) = parse_term(state).unwrap();
            let (_, is_done) = parser::done(state).unwrap();
            assert!(is_done);
            assert_eq!(term, *term2);
        }
    }
}
