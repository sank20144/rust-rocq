use std::fmt::Write as _;

pub enum Term {
    Atom(String),
    App(String, Vec<Term>),
    List(Vec<Term>),
    Str(String),
    Nat(u128),
    Int(i128),
    Bool(bool),
    Tuple(Vec<Term>),
}

pub fn atom(s: impl Into<String>) -> Term {
    Term::Atom(s.into())
}

pub fn app(head: impl Into<String>, args: Vec<Term>) -> Term {
    let head = head.into();
    if args.is_empty() {
        Term::Atom(head)
    } else {
        Term::App(head, args)
    }
}

pub fn string(s: impl Into<String>) -> Term {
    Term::Str(s.into())
}

pub fn nat(n: impl Into<u128>) -> Term {
    Term::Nat(n.into())
}

pub fn int(n: impl Into<i128>) -> Term {
    Term::Int(n.into())
}

pub fn boolean(b: bool) -> Term {
    Term::Bool(b)
}

pub fn list(items: Vec<Term>) -> Term {
    Term::List(items)
}

pub fn pair(a: Term, b: Term) -> Term {
    Term::Tuple(vec![a, b])
}

pub fn triple(a: Term, b: Term, c: Term) -> Term {
    Term::Tuple(vec![a, b, c])
}

pub fn option(t: Option<Term>) -> Term {
    match t {
        None => Term::Atom("None".to_owned()),
        Some(t) => Term::App("Some".to_owned(), vec![t]),
    }
}

impl Term {
    pub fn render(&self) -> String {
        let mut out = String::new();
        self.write(&mut out, false);
        out
    }

    fn write(&self, out: &mut String, nested: bool) {
        match self {
            Term::Atom(s) => out.push_str(s),
            Term::App(head, args) => {
                if nested {
                    out.push('(');
                }
                out.push_str(head);
                for a in args {
                    out.push(' ');
                    a.write(out, true);
                }
                if nested {
                    out.push(')');
                }
            }
            Term::List(items) => {
                out.push('[');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push_str("; ");
                    }
                    item.write(out, false);
                }
                out.push(']');
            }
            Term::Str(s) => {
                out.push('"');
                for c in s.chars() {
                    if c == '"' {
                        out.push_str("\"\"");
                    } else {
                        out.push(c);
                    }
                }
                out.push('"');
            }
            Term::Nat(n) => {
                let _ = write!(out, "{n}%nat");
            }
            Term::Int(n) => {
                if *n < 0 {
                    let _ = write!(out, "({n})%Z");
                } else {
                    let _ = write!(out, "{n}%Z");
                }
            }
            Term::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Term::Tuple(items) => {
                out.push('(');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    item.write(out, false);
                }
                out.push(')');
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_applications_get_parenthesised() {
        let t = app("TRef", vec![atom("RStatic"), app("TInt", vec![atom("W32")]), atom("Imm")]);
        assert_eq!(t.render(), "TRef RStatic (TInt W32) Imm");
    }

    #[test]
    fn lists_and_pairs_render_flat() {
        let t = list(vec![pair(int(0), nat(1u32)), pair(int(-2), nat(3u32))]);
        assert_eq!(t.render(), "[(0%Z, 1%nat); ((-2)%Z, 3%nat)]");
    }

    #[test]
    fn quotes_are_doubled() {
        assert_eq!(string("a\"b").render(), "\"a\"\"b\"");
    }

    #[test]
    fn triples_nest_to_the_left_like_rocq_does() {
        assert_eq!(triple(nat(1u32), nat(2u32), nat(3u32)).render(), "(1%nat, 2%nat, 3%nat)");
    }

    #[test]
    fn nullary_application_is_an_atom() {
        assert_eq!(app("TBool", vec![]).render(), "TBool");
    }
}
