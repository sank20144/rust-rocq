use std::fmt::Write as _;

const WIDTH: usize = 96;

pub enum Term {
    Atom(String),
    App(String, Vec<Term>),
    List(Vec<Term>),
    Str(String),
    Nat(u128),
    Int(i128),
    Bool(bool),
    Tuple(Vec<Term>),
    Note(String, Box<Term>),
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

pub fn note(label: impl Into<String>, t: Term) -> Term {
    Term::Note(label.into(), Box::new(t))
}

impl Term {
    pub fn render(&self) -> String {
        let mut out = String::new();
        self.write(&mut out, 0, false);
        out
    }

    fn width(&self) -> usize {
        match self {
            Term::Atom(s) => s.len(),
            Term::App(head, args) => {
                head.len() + args.iter().map(|a| 1 + a.width() + 2).sum::<usize>()
            }
            Term::List(items) | Term::Tuple(items) => {
                2 + items.iter().map(Term::width).sum::<usize>()
                    + 2 * items.len().saturating_sub(1)
            }
            Term::Str(s) => s.len() + s.matches('"').count() + 2,
            Term::Nat(n) => digits(*n),
            Term::Int(n) => digits(n.unsigned_abs()) + if *n < 0 { 6 } else { 2 },
            Term::Bool(b) => {
                if *b {
                    4
                } else {
                    5
                }
            }
            Term::Note(_, t) => t.width(),
        }
    }

    fn write(&self, out: &mut String, indent: usize, nested: bool) {
        if self.width() + indent <= WIDTH {
            self.write_flat(out, nested);
        } else {
            self.write_broken(out, indent, nested);
        }
    }

    fn write_flat(&self, out: &mut String, nested: bool) {
        match self {
            Term::Atom(s) => out.push_str(s),
            Term::App(head, args) => {
                if nested {
                    out.push('(');
                }
                out.push_str(head);
                for a in args {
                    out.push(' ');
                    a.write_flat(out, true);
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
                    item.write_flat(out, false);
                }
                out.push(']');
            }
            Term::Tuple(items) => {
                out.push('(');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    item.write_flat(out, false);
                }
                out.push(')');
            }
            Term::Str(s) => write_string(out, s),
            Term::Nat(n) => {
                let _ = write!(out, "{n}");
            }
            Term::Int(n) => {
                if *n < 0 {
                    let _ = write!(out, "({n})%Z");
                } else {
                    let _ = write!(out, "{n}%Z");
                }
            }
            Term::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
            Term::Note(_, t) => t.write_flat(out, nested),
        }
    }

    fn write_broken(&self, out: &mut String, indent: usize, nested: bool) {
        let inner = indent + 2;
        match self {
            Term::App(head, args) => {
                if nested {
                    out.push('(');
                }
                out.push_str(head);
                for a in args {
                    out.push('\n');
                    pad(out, inner);
                    if let Term::Note(label, t) = a {
                        let tagged = inner + label.len() + 7;
                        if t.width() + tagged <= WIDTH {
                            let _ = write!(out, "(* {label} *) ");
                            t.write_flat(out, true);
                        } else {
                            let _ = write!(out, "(* {label} *)\n");
                            pad(out, inner);
                            t.write(out, inner, true);
                        }
                    } else {
                        a.write(out, inner, true);
                    }
                }
                if nested {
                    out.push(')');
                }
            }
            Term::List(items) => {
                out.push_str("[ ");
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push('\n');
                        pad(out, indent);
                        out.push_str("; ");
                    }
                    if let Term::Note(label, t) = item {
                        let _ = write!(out, "(* {label} *)\n");
                        pad(out, inner);
                        t.write(out, inner, false);
                    } else {
                        item.write(out, inner, false);
                    }
                }
                out.push('\n');
                pad(out, indent);
                out.push(']');
            }
            Term::Tuple(items) => {
                out.push('(');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                        out.push('\n');
                        pad(out, inner);
                    }
                    item.write(out, inner, false);
                }
                out.push(')');
            }
            Term::Note(label, t) => {
                let _ = write!(out, "(* {label} *) ");
                t.write(out, indent, nested);
            }
            leaf => leaf.write_flat(out, nested),
        }
    }
}

fn pad(out: &mut String, n: usize) {
    out.extend(std::iter::repeat_n(' ', n));
}

fn write_string(out: &mut String, s: &str) {
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

fn digits(n: u128) -> usize {
    if n == 0 { 1 } else { n.ilog10() as usize + 1 }
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
        assert_eq!(t.render(), "[(0%Z, 1); ((-2)%Z, 3)]");
    }

    #[test]
    fn quotes_are_doubled() {
        assert_eq!(string("a\"b").render(), "\"a\"\"b\"");
    }

    #[test]
    fn triples_render_as_rocq_tuples() {
        assert_eq!(triple(nat(1u32), nat(2u32), nat(3u32)).render(), "(1, 2, 3)");
    }

    #[test]
    fn nullary_application_is_an_atom() {
        assert_eq!(app("TBool", vec![]).render(), "TBool");
    }

    #[test]
    fn notes_are_invisible_when_the_term_fits() {
        let t = app("Body", vec![note("name", string("f")), note("args", nat(2u32))]);
        assert_eq!(t.render(), "Body \"f\" 2");
    }

    #[test]
    fn wide_terms_break_and_pick_up_their_labels() {
        let wide = string("x".repeat(WIDTH));
        let t = app("Body", vec![note("name", wide), note("args", nat(2u32))]);
        let out = t.render();
        assert!(out.contains("(* name *)"), "{out}");
        assert!(out.contains("(* args *)"), "{out}");
        assert!(out.lines().count() >= 3, "{out}");
    }

    #[test]
    fn long_lists_break_one_element_per_line() {
        let items: Vec<Term> = (0..40).map(|i| app("BasicBlock", vec![nat(i as u32)])).collect();
        let out = list(items).render();
        assert!(out.starts_with("[ BasicBlock 0\n"), "{out}");
        assert!(out.contains("\n; BasicBlock 1"), "{out}");
        assert!(out.ends_with("\n]"), "{out}");
    }
}
