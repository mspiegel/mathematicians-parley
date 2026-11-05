//! Which theorems the Lean build covers.
//!
//! A theorem is in the Lean build exactly when every notation its page uses
//! and every item it cites has a Lean form: a notation with a `lean-builds`
//! field, a record with a `lean-proof` field, or a theorem of the corpus that
//! is itself in. Nothing lists the theorems; the build grows as fields are
//! added. A theorem left
//! out is reported with what keeps it out.

use indexmap::IndexMap;

use super::templates::Templates;
use crate::checker::CheckedCorpus;
use crate::corpus::cited_items;

/// Whether a theorem is in the Lean build.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Covered {
    In,
    /// Left out, and the first thing found that keeps it out.
    Out {
        reason: String,
    },
}

/// The notations the writer reads in code rather than by a `lean-builds` field:
/// letters, numerals, relations, memberships and quantifiers, whose Lean
/// form depends on the number types around them.
pub const IN_CODE: &[&str] = &[
    "name",
    "numeral",
    "equality",
    "order",
    "membership",
    "number-systems",
    "there-is",
    "for-all",
    "integer-range",
    "comma-conjunction",
    "function-type",
    "composition",
    "sum",
    "product",
    "tends-to",
    "series",
    "integral",
    "derivative",
    "function-limit",
    "continuous",
    "closed-interval",
    "there-is-some",
    "holds-of",
    "subset",
    "set-operations",
    "empty-set",
    "powerset",
    "set-builder",
    "singleton",
    "listed-two",
    "listed-three",
    "listed-four",
    "image",
    "one-to-one",
    "onto",
    "one-to-one-onto",
    "inverse",
    "set-image",
    "cardinality",
    "finite",
    "group-operation",
    "group-inverse",
    "subgroup",
    "coset",
    "polynomials",
    "is-a-polynomial",
    "sum-over",
    "product-over",
    "differentiable",
    "open",
    "open-interval",
    "indexed-union",
    "bijection",
];

/// Every theorem of the corpus, in or out.
/// `stated` are the library's items whose statements the build wrote.
pub fn coverage(
    checked: &CheckedCorpus,
    templates: &Templates,
    stated: &std::collections::BTreeSet<String>,
) -> IndexMap<String, Covered> {
    let mut out: IndexMap<String, Covered> = IndexMap::new();
    // A theorem citing another of the corpus is in only once that one is;
    // each pass settles at least the theorems whose citations are settled.
    loop {
        let mut changed = false;
        for thm in &checked.corpus.theorems {
            let name = thm.qualified();
            let covered = covered(checked, templates, stated, &name, &out);
            if out.get(&name) != Some(&covered) {
                out.insert(name, covered);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    out
}

/// Whether a step of a method other than citing a define, substituting from
/// one or a calculation cites a function the header lets by its value.
fn header_function_through_a_method(thm: &crate::corpus::Theorem) -> bool {
    let labels: Vec<&str> = thm
        .defines
        .iter()
        .filter(|d| d.line < thm.conclusion_line)
        .filter(|d| {
            matches!(
                crate::corpus::define_parts(&d.text),
                crate::outcome::Route::Built(crate::corpus::DefineParts::One(ref one))
                    if !one.params.is_empty()
            )
        })
        .map(|d| d.label.as_str())
        .collect();
    thm.steps.iter().any(|s| {
        // A calculation's rows citing the define put it in as a citation
        // of it does (`theorem::calculation`).
        let through = !matches!(
            s.just.head,
            crate::corpus::Head::Define
                | crate::corpus::Head::Method(
                    crate::corpus::Method::Substitute
                        | crate::corpus::Method::Calculation
                )
        );
        through && s.just.refs.iter().any(|r| labels.contains(&r.as_str()))
    })
}

/// Whether a line of the theorem puts the set letter among numbers, D ⊆ ℝ
/// or D ∈ 𝒫ℝ, which gives it the type of a set of those
/// (`items::numbers_subset`, `statement::introduces_in_set`).
fn among_numbers(name: &str, rec: &crate::checker::CheckedTheorem) -> bool {
    rec.page.entries().flat_map(|(_, n)| n.walk()).any(|n| {
        let [d, whole] = n.children.as_slice() else {
            return false;
        };
        let whole = match (&*n.notation_name(), whole.children.as_slice()) {
            ("subset", _) => whole,
            ("membership", [inner]) if &*whole.notation_name() == "powerset" => inner,
            _ => return false,
        };
        d.is_name() && *d.text == *name && set_of_numbers(whole)
    })
}

/// Whether a letter is a define whose value is a set of sets of numbers by
/// its shape, as the writer types a define by its value: {d ⊆ A : …} of a
/// set of numbers A, or {c ∈ O : …} of such a define O.
fn defined_parts_of_numbers(
    name: &str,
    thm: &crate::corpus::Theorem,
    rec: &crate::checker::CheckedTheorem,
    depth: usize,
) -> bool {
    if depth > 8 {
        return false;
    }
    let Some(line) = thm.defines.iter().find(|d| {
        matches!(crate::corpus::define_parts(&d.text),
            crate::outcome::Route::Built(crate::corpus::DefineParts::One(def))
                if def.name == name && def.params.is_empty())
    }) else {
        return false;
    };
    rec.page
        .entries()
        .filter(|(key, _)| key.line == line.line)
        .any(|(_, value)| parts_of_numbers(value, thm, rec, depth))
}

/// Whether a set term is a set of sets of numbers by its shape: {d ⊆ A : …}
/// of a set of numbers A, 𝒫A, or {c ∈ S : …} of such a term S.
fn parts_of_numbers(
    s: &crate::formula::Node,
    thm: &crate::corpus::Theorem,
    rec: &crate::checker::CheckedTheorem,
    depth: usize,
) -> bool {
    match (&*s.notation_name(), s.children.as_slice()) {
        ("set-builder-part", [_, whole, _]) => set_of_numbers(whole),
        ("set-builder", [_, whole, _]) => parts_of_numbers(whole, thm, rec, depth + 1),
        ("powerset", [whole]) => set_of_numbers(whole),
        _ => s.is_name() && defined_parts_of_numbers(&s.text, thm, rec, depth + 1),
    }
}

/// Whether a line gives the function letter a type between sets of numbers
/// by their shape, f : D → ℝ with D among numbers (`among_numbers`).
fn between_number_sets(name: &str, rec: &crate::checker::CheckedTheorem) -> bool {
    let of_numbers = |s: &crate::formula::Node| {
        set_of_numbers(s) || (s.is_name() && among_numbers(&s.text, rec))
    };
    rec.page.entries().flat_map(|(_, n)| n.walk()).any(|n| {
        matches!(n.children.as_slice(), [f, from, to]
            if n.notation() == crate::notations::FUNCTION_TYPE
                && f.is_name()
                && *f.text == *name
                && of_numbers(from)
                && of_numbers(to))
    })
}

/// Whether a set's members have a type its sort says, or, for A ∪ B, A ∩ B
/// or A ∖ B, its parts' sorts say.
fn sorted_set(s: &crate::formula::Node) -> bool {
    s.sort
        .full()
        .and_then(super::expr::Members::of_set)
        .is_some()
        || (&*s.notation_name() == "set-operations"
            && s.children.iter().all(sorted_set))
}

/// Whether a set lists letters, {B} or {a, b}: a set of the things they
/// are, as the writer reads it (`sets::members_of`).
fn listed_letters(s: &crate::formula::Node) -> bool {
    matches!(
        &*s.notation_name(),
        "singleton" | "listed-two" | "listed-three" | "listed-four"
    ) && s.children.iter().all(|c| c.is_name())
}

/// Whether a set is one of numbers by its shape: a number system, a letter
/// the checker sorts a set of numbers, or ℝ ∖ {2}, A ∪ B and A ∩ B of such.
fn set_of_numbers(s: &crate::formula::Node) -> bool {
    use crate::formula::Whole;
    if let Some(Whole::Set(m)) = s.sort.full() {
        return matches!(**m, Whole::Number);
    }
    match &*s.notation_name() {
        "number-systems" | "closed-interval" | "open-interval" | "integer-range" => {
            true
        }
        // A ∖ B holds what A does; A ∩ B what either does.
        "set-operations" => match (&*s.spelling().text(), s.children.as_slice()) {
            ("∖", [a, _]) => set_of_numbers(a),
            ("∩", [a, b]) => set_of_numbers(a) || set_of_numbers(b),
            (_, parts) => parts.iter().all(set_of_numbers),
        },
        // {2ⁿ : n ∈ ℤ} holds what its term is.
        "set-image" => s
            .children
            .first()
            .is_some_and(|term| term.sort.is("number")),
        _ => false,
    }
}

/// Whether a `let` line is `A be a set` or `x be an element` of a letter
/// whose sort Lean has a type for (`sets::set_letter_type`).
fn set_line(
    body: crate::formula::page::Written,
    rec: &crate::checker::CheckedTheorem,
) -> bool {
    use crate::sorts::introduction::{Form, Introduction};
    match Introduction::read(body).form {
        Form::Set(name)
        | Form::Element(name)
        | Form::Property { name, .. }
        | Form::FunctionOn { name, .. }
            if rec
                .sorts
                .get(&name)
                .is_some_and(|s| super::sets::set_letter_type(s).is_some()) =>
        {
            true
        }
        // An element a line puts in a set of numbers, A ∈ ℝ ∖ ℚ, is a number
        // of that set's type (`theorem::element_number_type`); one nothing
        // settles a sort of, a thing (`theorem::statement`).
        Form::Element(name) => {
            rec.sorts.get(&name).is_none()
                || rec.page.entries().flat_map(|(_, n)| n.walk()).any(|n| {
                    matches!(n.children.as_slice(), [x, set]
                if n.notation() == crate::notations::MEMBERSHIP
                    && x.is_name()
                    && *x.text == *name
                    && set_of_numbers(set))
                })
        }
        // A group is a type with Mathlib's group on it (`theorem::statement`);
        // a polynomial a function from ℂ to ℂ among set.mm's polynomials.
        Form::Group { .. } | Form::Polynomial(_) => true,
        _ => false,
    }
}

/// Whether what a `let` line asserts is a map between sets with a property,
/// `f : A → B is one-to-one`, onto, or both, its sets no number systems.
fn map_line(asserted: Option<&Vec<crate::formula::Node>>) -> bool {
    let map = |n: &crate::formula::Node| {
        matches!(
            &*n.notation_name(),
            "one-to-one" | "onto" | "one-to-one-onto"
        ) && {
            // Both sets of numbers, a function of numbers; or neither
            // touching a number system, a map of things.
            let sets = &n.children[1..];
            sets.iter().all(set_of_numbers)
                || sets.iter().all(|set| {
                    set.walk()
                        .iter()
                        .all(|m| m.notation() != crate::notations::NUMBER_SYSTEMS)
                })
        }
    };
    asserted.is_some_and(|a| !a.is_empty() && a.iter().all(map))
}

/// The function a proof's define line gives, where the Lean build writes it
/// (`Proof::define_function`): one argument, running over a number system,
/// `let S(m) = …, for m ∈ ℕ`. None for any other line.
pub fn defined_function(
    line: &crate::corpus::DefineLine,
    rec: &crate::checker::CheckedTheorem,
) -> Option<String> {
    let crate::outcome::Route::Built(crate::corpus::DefineParts::One(def)) =
        crate::corpus::define_parts(&line.text)
    else {
        return None;
    };
    let [param] = def.params.as_slice() else {
        return None;
    };
    let read: Vec<&crate::formula::Node> = rec
        .page
        .entries()
        .filter(|(key, _)| key.line == line.line)
        .map(|(_, node)| node)
        .collect();
    // Over a number system or a range of integers, {0, …, m}.
    let over_numbers = read.iter().any(|n| {
        (n.notation() == crate::notations::NUMBER_SYSTEMS
            && super::expr::system_of(n).is_some())
            || n.notation() == crate::notations::INTEGER_RANGE
    });
    let values = read
        .iter()
        .filter(|n| {
            !matches!(
                n.notation(),
                crate::notations::NUMBER_SYSTEMS | crate::notations::INTEGER_RANGE
            )
        })
        .filter(|n| !(n.is_name() && *n.text == *param.name))
        .count();
    (over_numbers && values == 1).then(|| def.name.clone())
}

fn covered(
    checked: &CheckedCorpus,
    templates: &Templates,
    stated: &std::collections::BTreeSet<String>,
    name: &str,
    so_far: &IndexMap<String, Covered>,
) -> Covered {
    let Some(thm) = checked
        .corpus
        .theorems
        .iter()
        .find(|t| t.qualified() == name)
    else {
        return Covered::Out {
            reason: "not a theorem of the corpus".to_string(),
        };
    };
    let Some(rec) = checked.theorems.get(name) else {
        return Covered::Out {
            reason: "the checker has not read it".to_string(),
        };
    };
    // Its file's functions written out where applied, as the writer reads
    // it (`theorem::outside_written`).
    let written = super::theorem::outside_written(checked, rec);
    let rec: &crate::checker::CheckedTheorem = &written;
    let set_valued = thm.defines.iter().any(|d| {
        matches!(crate::corpus::define_parts(&d.text),
            crate::outcome::Route::Built(crate::corpus::DefineParts::One(def))
                if !def.params.is_empty() && super::theorem::set_valued(rec, &def.name))
    });
    if set_valued {
        return Covered::Out {
            reason: super::theorem::SET_VALUED.to_string(),
        };
    }
    if !rec.problems.is_empty() {
        return Covered::Out {
            reason: "the checker refuses it".to_string(),
        };
    }
    // A `let` the page does not read as a formula is in where it is `A be a
    // set` or `x be an element` of a sort Lean has a type for, or a map
    // between sets with a property, `let f : A → B be one-to-one`, which
    // the writer states from what the checker reads the line to assert.
    let in_parts = thm.hypotheses.iter().enumerate().any(|(i, h)| {
        let body = h.body(&thm.path);
        let unread = body.sentences().iter().any(|s| rec.page.get(s).is_none());
        unread && !set_line(body, rec) && !map_line(rec.asserted.get(i))
    });
    if in_parts {
        return Covered::Out {
            reason: "a let line says a property beside a type, which the Lean build does not read yet"
                .to_string(),
        };
    }
    // A function the header lets by its value is its equation for every x
    // (`theorem::header_function`), which a step citing the define or
    // substituting from it puts in; a step of another method citing it, an
    // algebra or a transitivity from D1, does not.
    if header_function_through_a_method(thm) {
        return Covered::Out {
            reason: "a step cites a function the header lets through a method, which its equation for every x is not put in by"
                .to_string(),
        };
    }
    // A count of a set no line says is finite is in ℕ∞ (`sets::count_term`),
    // whose subtraction stops at 0 where the page's does not: |A| − |B| is
    // not written of such sets.
    // The theorem counts as natural numbers the sets its hypotheses make
    // finite (`theorem::finite_lines`).
    let mut finite = super::sets::finite_sets(
        &checked.grammar,
        &super::theorem::finite_lines(thm, rec),
    );
    super::theorem::finite_named(&checked.grammar, thm, rec, &mut finite);
    let extended = |n: &crate::formula::Node| {
        super::sets::counts_in_extended(&checked.grammar, &finite, n)
    };
    // Nor is one compared with what is no natural number, which beside it
    // is taken in ℕ: a difference or a quotient, |S| = j − 1, or a letter
    // the page puts in ℤ, ℚ, ℝ or ℂ, |S| = j of j ∈ ℤ.
    let systems: std::collections::BTreeMap<String, super::expr::System> = rec
        .page
        .entries()
        .filter_map(|(_, n)| super::statement::introduces(n))
        .collect();
    let differs = |n: &crate::formula::Node| {
        n.walk().iter().any(|m| {
            let lettered = m.is_name()
                && matches!(
                    systems.get(m.text.as_str()),
                    Some(super::expr::System::Type(_))
                );
            lettered
                || (matches!(&*m.notation_name(), "additive" | "multiplicative")
                    && !matches!(&*m.spelling().text(), "+" | "·"))
        })
    };
    let count_subtracted =
        rec.page
            .entries()
            .flat_map(|(_, node)| node.walk())
            .any(|n| {
                let arithmetic =
                    matches!(&*n.notation_name(), "additive" | "multiplicative");
                let plus_or_times = matches!(&*n.spelling().text(), "+" | "·");
                let beside = match n.children.as_slice() {
                    [a, b] if matches!(&*n.notation_name(), "equality" | "order") => {
                        (extended(a) && differs(b)) || (extended(b) && differs(a))
                    }
                    _ => false,
                };
                (arithmetic && !plus_or_times && extended(&n)) || beside
            });
    if count_subtracted {
        return Covered::Out {
            reason: "a count of a set subtracted or divided, which ℕ∞ does not compute as the page does"
                .to_string(),
        };
    }
    // A citation that gives a count for a letter of a number system, m :=
    // |A| for m ∈ ℕ₀, of a set no line says is finite: the count is in ℕ∞,
    // the letter in Lean's ℕ. A count inside a formula or a set given for
    // a letter of those, P := "k ≤ |W| and …", is written as the lines
    // around it write it.
    let count_given = rec
        .cited
        .iter()
        .flatten()
        .chain(rec.cited_requires.values())
        .any(|c| {
            c.binding
                .values()
                .any(|v| v.sort.is("number") && extended(v))
        });
    if count_given {
        return Covered::Out {
            reason: "a count given for a number letter of a cited item, which Lean's ℕ meets in ℕ∞ only through finiteness"
                .to_string(),
        };
    }
    // A letter the page gives a function type, `f : ℝ → ℝ`, is a Lean
    // function of its own; a composite of such is one too; and so is a
    // function the proof defines, `let S(m) = …, for m ∈ ℕ`.
    let mut own: std::collections::BTreeSet<String> = rec
        .page
        .entries()
        .flat_map(|(_, node)| node.walk())
        .filter(|n| n.notation() == crate::notations::FUNCTION_TYPE)
        .filter_map(|n| {
            n.children
                .first()
                .filter(|f| f.is_name())
                .map(|f| f.text.to_string())
        })
        .collect();
    // A polynomial is a function from ℂ to ℂ (`sets::polynomial_claim`): a
    // letter the page says is one, in a line or a `let`, or that "there is
    // a polynomial q" binds.
    let said = rec
        .page
        .entries()
        .map(|(_, node)| node)
        .chain(rec.asserted.iter().flatten())
        .flat_map(|node| node.walk());
    for n in said {
        if let Some(p) = super::statement::introduces_polynomial(&n) {
            own.insert(p);
        }
        let over_polynomials = matches!(n.children.as_slice(), [q, set, _]
            if matches!(n.notation(), crate::notations::THERE_IS | crate::notations::FOR_ALL)
                && &*set.notation_name() == "polynomials"
                && q.is_name());
        if over_polynomials {
            own.insert(n.children[0].text.to_string());
        }
    }
    // Only a define in the proof below the statement: one in the statement
    // is part of what the theorem says, which the statement writer reads.
    for line in thm.defines.iter().filter(|d| d.line > thm.conclusion_line) {
        if let Some(name) = defined_function(line, rec) {
            own.insert(name);
        }
    }
    // A recursion over ℕ₀ the statement lets is its functions, letters of
    // the statement (`theorem::header_recursions`), as is a function it lets
    // by its value over numbers (`theorem::header_function`).
    for line in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        if let Some(name) = defined_function(line, rec) {
            own.insert(name);
        }
        if let crate::outcome::Route::Built(crate::corpus::DefineParts::Recursion(r)) =
            crate::corpus::define_parts(&line.text)
        {
            if r.domain.trim() == "ℕ₀" {
                own.extend(r.names.iter().cloned());
            }
        }
    }
    // A library function applied is in where its definition says what it
    // is in Lean (`lean-builds`).
    let mut notations: Vec<String> = rec
        .page
        .entries()
        .flat_map(|(_, node)| node.walk())
        .filter_map(|n| {
            let name = n.notation_name().to_string();
            if matches!(name.as_str(), "application" | "application-to-two") {
                let head = n.children.first()?;
                if !head.is_name() || own.contains(head.text.as_str()) {
                    return None;
                }
                let f = head.text.to_string();
                return templates.function(&f).is_none().then(|| {
                    format!("{f}, applied, whose definition has no lean-builds field")
                });
            }
            // f is a function on a set, which a Lean function of the set's
            // type is (`expr`): a set of numbers, a range, or a set of
            // things a letter's sort says.
            // Continuity or a derivative of f′: its domain is where f has a
            // derivative, which no line gives (`expr::differentiable`).
            if matches!(name.as_str(), "continuous" | "differentiable")
                && n.children.first().is_some_and(|f| !f.is_name())
            {
                return Some(format!("{name} of a function that is no letter"));
            }
            if &*n.notation_name() == "function-on" {
                let typed = matches!(n.children.as_slice(), [_, set]
                    if set_of_numbers(set)
                        || set.notation() == crate::notations::INTEGER_RANGE
                        || sorted_set(set));
                return (!typed)
                    .then(|| "a function on a set Lean has no type for".to_string());
            }
            if n.notation() == crate::notations::FUNCTION_TYPE {
                // Between number systems, between sets of things, a map
                // `α → α` (`sets`), or between sets of numbers, a function of
                // the numbers' types with the sets beside it.
                // The sets are the last two parts, after the letter where
                // the type names one.
                let sides = n.children.len().checked_sub(2).map(|k| &n.children[k..]);
                let typed = matches!(sides, Some([from, to])
                if super::expr::function_systems(from, to).is_some()
                    || [from, to].iter().all(|s| {
                        sorted_set(s)
                            || listed_letters(s)
                            || &*s.notation_name() == "empty-set"
                    })
                    || [from, to].iter().all(|s| set_of_numbers(s)));
                return (!typed).then(|| {
                    "a function type between sets Lean has no type for yet".to_string()
                });
            }
            (!IN_CODE.contains(&name.as_str()) && !templates.maps(&name))
                .then(|| format!("notation {name}, which has no lean-builds field"))
        })
        .collect();
    notations.sort();
    if let Some(first) = notations.first() {
        return Covered::Out {
            reason: format!("it writes {first}"),
        };
    }
    // A letter whose sort Lean has no type for yet: the writer types
    // numbers only.
    let mut letters: Vec<(String, String)> = rec
        .page
        .entries()
        .flat_map(|(_, node)| node.walk())
        .filter(|n| n.is_name() && templates.function(&n.text).is_none())
        .filter(|n| !own.contains(n.text.as_str()))
        .filter_map(|n| {
            let sort = rec.sorts.get(n.text.as_str())?;
            // A group's elements, the group itself and its subgroups take
            // their types from the group line (`theorem::statement`).
            let of_group =
                matches!(sort.full(), Some(crate::formula::Whole::GroupElement))
                    || matches!(sort.full(), Some(crate::formula::Whole::Set(m))
                    if matches!(**m, crate::formula::Whole::GroupElement));
            // A set of numbers a line puts among numbers, D ⊆ ℝ, is a set of
            // those; a function of numbers is typed through its sets.
            let of_numbers = match sort.full() {
                Some(crate::formula::Whole::Set(m)) => match &**m {
                    crate::formula::Whole::Number => among_numbers(&n.text, rec),
                    crate::formula::Whole::Set(inner) => {
                        matches!(**inner, crate::formula::Whole::Number)
                            && defined_parts_of_numbers(&n.text, thm, rec, 0)
                    }
                    _ => false,
                },
                Some(crate::formula::Whole::Function(_, _)) => {
                    between_number_sets(&n.text, rec)
                }
                _ => false,
            };
            let typed = sort.is("number")
                || super::sets::set_letter_type(sort).is_some()
                || of_group
                || of_numbers;
            (!typed).then(|| (n.text.to_string(), sort.describe()))
        })
        .collect();
    letters.sort();
    if let Some((letter, sort)) = letters.first() {
        return Covered::Out {
            reason: format!("{letter} is {sort}, which has no Lean type yet"),
        };
    }
    for (full, _) in cited_items(thm) {
        if let Some(record) = super::items::record_of(checked, &full) {
            // An item the Lean build cannot use yet keeps out what cites
            // it, and so does one proved by a Parley proof the build
            // leaves out; one with nothing to prove, or with Mathlib's
            // proof or a bridge, does not.
            use crate::corpus::records::Provided;
            match record.lean_provided() {
                Some(Provided::NotYet) | None => {
                    return Covered::Out {
                        reason: format!("{full}'s lean-proof is not yet implemented"),
                    };
                }
                Some(Provided::Proof(proof)) => {
                    if !matches!(so_far.get(proof), Some(Covered::In)) {
                        return Covered::Out {
                            reason: format!(
                                "{full} is proved by {proof}, which is not in the Lean build"
                            ),
                        };
                    }
                }
                // A proof whose item's statement the build could not write,
                // a phrase whose meaning it cannot state, is no proof yet.
                Some(Provided::By(_)) if !stated.contains(&full) => {
                    return Covered::Out {
                        reason: format!("{full}'s statement is not in the Lean build"),
                    };
                }
                Some(Provided::By(_) | Provided::Nothing) => {}
            }
            continue;
        }
        match so_far.get(&full) {
            Some(Covered::In) => {}
            _ => {
                return Covered::Out {
                    reason: format!("{full} is not in the Lean build"),
                }
            }
        }
    }
    Covered::In
}
