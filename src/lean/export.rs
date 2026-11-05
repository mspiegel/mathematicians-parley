//! What Lean proved, as lean4export writes it.
//!
//! lean4export writes a Lean environment as lines of JSON: each name, each
//! universe level and each expression numbered, and each declaration by the
//! numbers of its name, type and value (`format_ndjson.md` in its
//! repository). This reads the names, the expressions and the declarations,
//! and answers two questions of a declaration: which axioms it rests on, and
//! which arithmetic its statement does in which type.

use std::collections::{BTreeMap, BTreeSet};

use indexmap::IndexMap;
use serde_json::Value;

/// An expression, by the numbers of its parts.
#[derive(Clone, Debug)]
pub enum Expr {
    Bvar,
    Sort,
    Const(usize),
    App {
        func: usize,
        arg: usize,
    },
    Binder {
        ty: usize,
        body: usize,
    },
    Let {
        ty: usize,
        value: usize,
        body: usize,
    },
    Lit,
    Proj {
        inner: usize,
    },
    Mdata {
        inner: usize,
    },
}

/// A declaration: its kind, and the numbers of its type and value.
#[derive(Clone, Debug)]
pub struct Decl {
    pub kind: String,
    pub ty: usize,
    pub value: Option<usize>,
    /// The constants an inductive type's declaration makes besides itself.
    pub made: Vec<String>,
}

/// A declaration as its line writes it, before every name is read.
struct Read {
    kind: String,
    /// Its name's number; None for an inductive declaration, which holds
    /// the names of what it makes instead.
    name: Option<usize>,
    ty: usize,
    value: Option<usize>,
    /// The numbers of the names an inductive declaration makes.
    made: Vec<usize>,
}

/// An export, read.
#[derive(Default)]
pub struct Export {
    names: Vec<Option<String>>,
    exprs: Vec<Option<Expr>>,
    pub decls: IndexMap<String, Decl>,
}

fn at<T: Clone>(v: &mut Vec<Option<T>>, i: usize, x: T) {
    if v.len() <= i {
        v.resize(i + 1, None);
    }
    v[i] = Some(x);
}

fn num(v: &Value, key: &str) -> Option<usize> {
    v.get(key)?.as_u64().map(|n| n as usize)
}

impl Export {
    /// The lines lean4export wrote; a line that does not read is reported
    /// with its number.
    pub fn read(text: &str) -> Result<Export, String> {
        let mut out = Export::default();
        // The anonymous name.
        at(&mut out.names, 0, String::new());
        let mut decls: Vec<Read> = Vec::new();
        for (n, line) in text.lines().enumerate() {
            if line.is_empty() {
                continue;
            }
            let v: Value = serde_json::from_str(line).map_err(|e| {
                format!("line {} of the export does not read: {e}", n + 1)
            })?;
            if let Some(id) = num(&v, "in") {
                let name = if let Some(s) = v.get("str") {
                    let pre = num(s, "pre").unwrap_or(0);
                    let part = s.get("str").and_then(Value::as_str).unwrap_or("");
                    out.join(pre, part)
                } else if let Some(s) = v.get("num") {
                    let pre = num(s, "pre").unwrap_or(0);
                    let i = s.get("i").and_then(Value::as_u64).unwrap_or(0);
                    out.join(pre, &i.to_string())
                } else {
                    String::new()
                };
                at(&mut out.names, id, name);
                continue;
            }
            if let Some(id) = num(&v, "ie") {
                let expr = if v.get("bvar").is_some() {
                    Expr::Bvar
                } else if v.get("sort").is_some() {
                    Expr::Sort
                } else if let Some(c) = v.get("const") {
                    Expr::Const(num(c, "name").unwrap_or(0))
                } else if let Some(a) = v.get("app") {
                    Expr::App {
                        func: num(a, "fn").unwrap_or(0),
                        arg: num(a, "arg").unwrap_or(0),
                    }
                } else if let Some(b) = v.get("lam").or_else(|| v.get("forallE")) {
                    Expr::Binder {
                        ty: num(b, "type").unwrap_or(0),
                        body: num(b, "body").unwrap_or(0),
                    }
                } else if let Some(l) = v.get("letE") {
                    Expr::Let {
                        ty: num(l, "type").unwrap_or(0),
                        value: num(l, "value").unwrap_or(0),
                        body: num(l, "body").unwrap_or(0),
                    }
                } else if let Some(p) = v.get("proj") {
                    Expr::Proj {
                        inner: num(p, "struct").unwrap_or(0),
                    }
                } else if let Some(m) = v.get("mdata") {
                    Expr::Mdata {
                        inner: num(m, "expr").unwrap_or(0),
                    }
                } else {
                    Expr::Lit
                };
                at(&mut out.exprs, id, expr);
                continue;
            }
            if num(&v, "il").is_some() || v.get("meta").is_some() {
                continue;
            }
            // A declaration: one key, its kind.
            let Some((kind, body)) = v.as_object().and_then(|o| o.iter().next()) else {
                continue;
            };
            let made: Vec<usize> = match kind.as_str() {
                "inductive" => {
                    let names = |key: &str| -> Vec<usize> {
                        body.get(key)
                            .and_then(Value::as_array)
                            .map(|all| {
                                all.iter().filter_map(|x| num(x, "name")).collect()
                            })
                            .unwrap_or_default()
                    };
                    let mut all = names("types");
                    all.extend(names("ctors"));
                    all.extend(names("recs"));
                    all
                }
                _ => Vec::new(),
            };
            let (Some(name), Some(ty)) = (num(body, "name"), num(body, "type")) else {
                // An inductive declaration holds its types inside it.
                if kind == "inductive" {
                    decls.push(Read {
                        kind: kind.clone(),
                        name: None,
                        ty: 0,
                        value: None,
                        made,
                    });
                }
                continue;
            };
            decls.push(Read {
                kind: kind.clone(),
                name: Some(name),
                ty,
                value: num(body, "value"),
                made,
            });
        }
        for Read {
            kind,
            name,
            ty,
            value,
            made,
        } in decls
        {
            let made: Vec<String> = made.iter().map(|m| out.name(*m)).collect();
            let Some(name) = name else {
                // Each type, constructor and recursor of an inductive is a
                // constant an expression may name, and none is an axiom.
                for m in &made {
                    out.decls.insert(
                        m.clone(),
                        Decl {
                            kind: kind.clone(),
                            ty: 0,
                            value: None,
                            made: Vec::new(),
                        },
                    );
                }
                continue;
            };
            out.decls.insert(
                out.name(name),
                Decl {
                    kind,
                    ty,
                    value,
                    made,
                },
            );
        }
        Ok(out)
    }

    fn join(&self, pre: usize, part: &str) -> String {
        let before = self.name(pre);
        if before.is_empty() {
            part.to_string()
        } else {
            format!("{before}.{part}")
        }
    }

    /// The name numbered `id`.
    pub fn name(&self, id: usize) -> String {
        self.names.get(id).cloned().flatten().unwrap_or_default()
    }

    fn expr(&self, id: usize) -> Option<&Expr> {
        self.exprs.get(id).and_then(Option::as_ref)
    }

    /// The constants an expression names.
    fn constants(&self, root: usize, out: &mut BTreeSet<String>) {
        let mut stack = vec![root];
        let mut seen = BTreeSet::new();
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            match self.expr(id) {
                Some(Expr::Const(n)) => {
                    out.insert(self.name(*n));
                }
                Some(Expr::App { func, arg }) => stack.extend([*func, *arg]),
                Some(Expr::Binder { ty, body }) => stack.extend([*ty, *body]),
                Some(Expr::Let { ty, value, body }) => {
                    stack.extend([*ty, *value, *body])
                }
                Some(Expr::Proj { inner } | Expr::Mdata { inner }) => {
                    stack.push(*inner)
                }
                _ => {}
            }
        }
    }

    /// Every axiom a declaration rests on, through the types and values of
    /// every constant it reaches.
    pub fn axioms(&self, decl: &str) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        let mut seen: BTreeSet<String> = BTreeSet::new();
        let mut stack = vec![decl.to_string()];
        while let Some(name) = stack.pop() {
            if !seen.insert(name.clone()) {
                continue;
            }
            let Some(d) = self.decls.get(&name) else {
                continue;
            };
            if d.kind == "axiom" {
                out.insert(name.clone());
            }
            let mut reached = BTreeSet::new();
            if d.ty != 0 || d.kind != "inductive" {
                self.constants(d.ty, &mut reached);
            }
            if let Some(v) = d.value {
                self.constants(v, &mut reached);
            }
            stack.extend(reached.into_iter().filter(|r| !seen.contains(r)));
        }
        out
    }

    /// The head constant of an application and its arguments, in order.
    fn spine(&self, id: usize) -> (Option<String>, Vec<usize>) {
        let mut args = Vec::new();
        let mut at = id;
        loop {
            match self.expr(at) {
                Some(Expr::App { func, arg }) => {
                    args.push(*arg);
                    at = *func;
                }
                Some(Expr::Mdata { inner }) => at = *inner,
                Some(Expr::Const(n)) => {
                    args.reverse();
                    return (Some(self.name(*n)), args);
                }
                _ => {
                    args.reverse();
                    return (None, args);
                }
            }
        }
    }

    /// Each arithmetic operation a declaration's statement does, by the
    /// operation and the type it is done in, counted.
    pub fn arithmetic(&self, decl: &str) -> BTreeMap<(String, String), usize> {
        let mut out = BTreeMap::new();
        let Some(d) = self.decls.get(decl) else {
            return out;
        };
        let mut stack = vec![d.ty];
        while let Some(id) = stack.pop() {
            match self.expr(id) {
                Some(Expr::App { .. }) => {
                    let (head, mut args) = self.spine(id);
                    // A case split's instance deciding its condition,
                    // `Classical.propDecidable (x < 1/2)`, says the condition
                    // again and does no arithmetic of its own.
                    if matches!(head.as_deref(), Some("ite" | "dite")) && args.len() > 2
                    {
                        args.remove(2);
                    }
                    if let Some(op) = head.as_deref().and_then(operation) {
                        let ty = args
                            .first()
                            .and_then(|t| self.spine(*t).0)
                            .unwrap_or_default();
                        *out.entry((op.to_string(), ty)).or_insert(0) += 1;
                    }
                    stack.extend(args);
                }
                Some(Expr::Binder { ty, body }) => stack.extend([*ty, *body]),
                Some(Expr::Let { ty, value, body }) => {
                    stack.extend([*ty, *value, *body])
                }
                Some(Expr::Proj { inner } | Expr::Mdata { inner }) => {
                    stack.push(*inner)
                }
                _ => {}
            }
        }
        out
    }
}

/// The page's name for a Lean arithmetic operation, by its constant; None
/// for any other constant.
pub fn operation(constant: &str) -> Option<&'static str> {
    Some(match constant {
        "HAdd.hAdd" => "addition",
        "HSub.hSub" => "subtraction",
        "HMul.hMul" => "multiplication",
        "HDiv.hDiv" => "division",
        "HPow.hPow" => "power",
        "Neg.neg" => "negation",
        _ => return None,
    })
}

/// The axioms every Lean proof may rest on: those of Lean's own logic.
pub const STANDARD_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

/// Why an operation in a type is not the page's: subtraction and negation
/// in ℕ stop at 0, and division in ℕ or ℤ rounds down. None where the type
/// computes as the page does.
pub fn unfaithful(op: &str, ty: &str) -> Option<String> {
    match (op, ty) {
        ("subtraction" | "negation", "Nat") => {
            Some(format!("{op} in ℕ, where it stops at 0"))
        }
        ("division", "Nat" | "Int") => Some(format!(
            "division in {}, where it rounds down",
            if ty == "Nat" { "ℕ" } else { "ℤ" }
        )),
        _ => None,
    }
}
