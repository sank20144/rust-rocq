use std::collections::BTreeSet;
use std::iter;

const WIDTH: usize = 96;

pub enum Term {
    Atom(String),
    App(String, Vec<Term>),
    List(Vec<Term>),
    Str(String),
    Nat(u128),
    Int(i128),
    Bits(u128),
    Bool(bool),
    Tuple(Vec<Term>),
    Note(String, Box<Term>),
}

pub fn atom(name: &str) -> Term {
    Term::Atom(name.to_owned())
}

pub fn app(head: &str, args: Vec<Term>) -> Term {
    if args.is_empty() {
        Term::Atom(head.to_owned())
    } else {
        Term::App(head.to_owned(), args)
    }
}

pub fn string(text: &str) -> Term {
    Term::Str(text.to_owned())
}

pub fn nat(n: u64) -> Term {
    Term::Nat(u128::from(n))
}

pub fn int(n: i128) -> Term {
    Term::Int(n)
}

pub fn bits(n: u128) -> Term {
    Term::Bits(n)
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

#[cfg(test)]
pub fn triple(a: Term, b: Term, c: Term) -> Term {
    Term::Tuple(vec![a, b, c])
}

pub fn option(t: Option<Term>) -> Term {
    match t {
        None => Term::Atom("None".to_owned()),
        Some(t) => Term::App("Some".to_owned(), vec![t]),
    }
}

pub fn note(label: &str, t: Term) -> Term {
    Term::Note(label.to_owned(), Box::new(t))
}

impl Term {
    pub fn collect_heads(&self, heads: &mut BTreeSet<String>) {
        match self {
            Term::Atom(atom) => {
                heads.insert(atom.clone());
            }
            Term::App(head, args) => {
                heads.insert(head.clone());
                for arg in args {
                    arg.collect_heads(heads);
                }
            }
            Term::List(items) | Term::Tuple(items) => {
                for item in items {
                    item.collect_heads(heads);
                }
            }
            Term::Note(_, term) => term.collect_heads(heads),
            Term::Str(_) | Term::Nat(_) | Term::Int(_) | Term::Bits(_) | Term::Bool(_) => {}
        }
    }

    pub fn render(&self) -> String {
        self.render_at(0)
    }

    pub fn render_at(&self, indent: usize) -> String {
        let mut out = String::new();
        self.write(&mut out, indent, false);
        out
    }

    fn width(&self) -> usize {
        match self {
            Term::Atom(s) => s.len(),
            Term::App(head, args) => {
                head.len() + args.iter().map(|a| 1 + a.width() + 2).sum::<usize>()
            }
            Term::List(items) | Term::Tuple(items) => {
                2 + items.iter().map(Term::width).sum::<usize>() + 2 * items.len().saturating_sub(1)
            }
            Term::Str(s) => s.len() + s.matches('"').count() + 2,
            Term::Nat(n) => digits(*n),
            Term::Bits(n) => digits(*n) + 2,
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
        use std::fmt::Write as _;

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
            Term::Bits(n) => {
                let _ = write!(out, "{n}%Z");
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
        use std::fmt::Write as _;

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
    out.extend(iter::repeat_n(' ', n));
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
    if n == 0 {
        1
    } else {
        n.ilog10() as usize + 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_applications_get_parenthesised() {
        let t = app(
            "TRef",
            vec![atom("RStatic"), app("TInt", vec![atom("W32")]), atom("Imm")],
        );
        assert_eq!(t.render(), "TRef RStatic (TInt W32) Imm");
    }

    #[test]
    fn lists_and_pairs_render_flat() {
        let t = list(vec![pair(int(0), nat(1)), pair(int(-2), nat(3))]);
        assert_eq!(t.render(), "[(0%Z, 1); ((-2)%Z, 3)]");
    }

    #[test]
    fn quotes_are_doubled() {
        assert_eq!(string("a\"b").render(), "\"a\"\"b\"");
    }

    #[test]
    fn triples_render_as_rocq_tuples() {
        assert_eq!(triple(nat(1), nat(2), nat(3)).render(), "(1, 2, 3)");
    }

    #[test]
    fn nullary_application_is_an_atom() {
        assert_eq!(app("TBool", vec![]).render(), "TBool");
    }

    #[test]
    fn notes_are_invisible_when_the_term_fits() {
        let t = app(
            "Body",
            vec![note("name", string("f")), note("args", nat(2))],
        );
        assert_eq!(t.render(), "Body \"f\" 2");
    }

    #[test]
    fn wide_terms_break_and_pick_up_their_labels() {
        let wide = string(&"x".repeat(WIDTH));
        let t = app("Body", vec![note("name", wide), note("args", nat(2))]);
        let out = t.render();
        assert!(out.contains("(* name *)"), "{out}");
        assert!(out.contains("(* args *)"), "{out}");
        assert!(out.lines().count() >= 3, "{out}");
    }

    #[test]
    fn long_lists_break_one_element_per_line() {
        let items: Vec<Term> = (0..40).map(|i| app("BasicBlock", vec![nat(i)])).collect();
        let out = list(items).render();
        assert!(out.starts_with("[ BasicBlock 0\n"), "{out}");
        assert!(out.contains("\n; BasicBlock 1"), "{out}");
        assert!(out.ends_with("\n]"), "{out}");
    }

    #[test]
    fn constructor_coverage_ignores_data_and_comments() {
        let t = note(
            "ignored",
            app(
                "Body",
                vec![app("TInt", vec![atom("W32")]), string("TBool")],
            ),
        );
        let mut heads = BTreeSet::new();
        t.collect_heads(&mut heads);
        assert_eq!(
            heads.into_iter().collect::<Vec<_>>(),
            vec!["Body", "TInt", "W32"]
        );
    }
}
