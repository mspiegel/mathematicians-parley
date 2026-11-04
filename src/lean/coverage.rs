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
];

/// Every theorem of the corpus, in or out.
pub fn coverage(
    checked: &CheckedCorpus,
    templates: &Templates,
) -> IndexMap<String, Covered> {
    let mut out: IndexMap<String, Covered> = IndexMap::new();
    // A theorem citing another of the corpus is in only once that one is;
    // each pass settles at least the theorems whose citations are settled.
    loop {
        let mut changed = false;
        for thm in &checked.corpus.theorems {
            let name = thm.qualified();
            let covered = covered(checked, templates, &name, &out);
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

/// Whether a let of the theorem names a quotient as a whole number, `let e
/// = p/d, a positive integer`: a kind of whole number, and a value with a
/// division outside any floor (⌊A/B⌋ is a whole number as written).
fn kinded_quotient(
    thm: &crate::corpus::Theorem,
    rec: &crate::checker::CheckedTheorem,
) -> bool {
    thm.defines.iter().any(|d| {
        let crate::outcome::Route::Built(crate::corpus::DefineParts::One(one)) =
            crate::corpus::define_parts(&d.text)
        else {
            return false;
        };
        let whole = matches!(
            one.kind.as_deref(),
            Some(
                "a positive integer"
                    | "an integer"
                    | "a natural number"
                    | "a nonnegative integer"
            )
        );
        whole
            && rec
                .page
                .entries()
                .filter(|(key, _)| key.line == d.line)
                .any(|(_, n)| divides_outside_floor(n))
    })
}

/// Whether a term with a letter a line says is an integer, a·x + b·y of
/// x ∈ ℤ, is said to be in a set a define builds of naturals, S = {t ∈ ℕ :
/// …}.
fn integer_in_natural_set(
    thm: &crate::corpus::Theorem,
    rec: &crate::checker::CheckedTheorem,
) -> bool {
    use super::expr::{system_of, System};
    let nodes: Vec<crate::formula::Node> =
        rec.page.entries().flat_map(|(_, n)| n.walk()).collect();
    let integers: Vec<&str> = nodes
        .iter()
        .filter_map(|n| match n.children.as_slice() {
            [x, set]
                if n.notation() == crate::notations::MEMBERSHIP
                    && x.is_name()
                    && system_of(set)
                        == Some(System::Type(super::templates::Num::Int)) =>
            {
                Some(&*x.text)
            }
            _ => None,
        })
        .collect();
    let natural_sets: Vec<String> = thm
        .defines
        .iter()
        .filter_map(|d| {
            let crate::outcome::Route::Built(crate::corpus::DefineParts::One(one)) =
                crate::corpus::define_parts(&d.text)
            else {
                return None;
            };
            let of_naturals = rec
                .page
                .entries()
                .filter(|(key, _)| key.line == d.line)
                .any(
                    |(_, n)| match (&*n.notation_name(), n.children.as_slice()) {
                        ("set-builder", [_, over, _]) => matches!(
                            system_of(over),
                            Some(System::Positive | System::NonNegative)
                        ),
                        _ => false,
                    },
                );
            of_naturals.then_some(one.name)
        })
        .collect();
    nodes.iter().any(|n| {
        matches!(n.children.as_slice(), [t, s]
            if n.notation() == crate::notations::MEMBERSHIP
                && !t.is_name()
                && s.is_name()
                && natural_sets.iter().any(|name| *name == *s.text)
                && t.walk().iter().any(|m| m.is_name() && integers.contains(&&*m.text)))
    })
}

/// Whether a term divides somewhere a floor does not hold.
fn divides_outside_floor(n: &crate::formula::Node) -> bool {
    if &*n.notation_name() == "floor" {
        return false;
    }
    n.spelling() == crate::notations::DIVIDED
        || n.children.iter().any(divides_outside_floor)
}

/// Whether the theorem cites the set-image item and writes a set-image over
/// ℤ whose term raises something to its index, {9ⁿ : n ∈ ℤ}: rationals of
/// an integer, which the item's map of one type cannot take.
fn image_of_powers_cited(
    thm: &crate::corpus::Theorem,
    rec: &crate::checker::CheckedTheorem,
) -> bool {
    let cites = cited_items(thm)
        .iter()
        .any(|(full, _)| full == "stdlib/functions/set-image");
    cites
        && rec.page.entries().flat_map(|(_, n)| n.walk()).any(|n| {
            matches!((&*n.notation_name(), n.children.as_slice()), ("set-image", [term, index, set])
                if super::expr::system_of(set)
                    == Some(super::expr::System::Type(super::templates::Num::Int))
                    && term.walk().iter().any(|p| {
                        p.notation() == crate::notations::POWER
                            && p.children.get(1).is_some_and(|e| {
                                e.walk().iter().any(|x| x.is_name() && x.text == index.text)
                            })
                    }))
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

/// Whether a set is one of numbers by its shape: a number system, a letter
/// the checker sorts a set of numbers, or ℝ ∖ {2}, A ∪ B and A ∩ B of such.
fn set_of_numbers(s: &crate::formula::Node) -> bool {
    use crate::formula::Whole;
    if let Some(Whole::Set(m)) = s.sort.full() {
        return matches!(**m, Whole::Number);
    }
    match &*s.notation_name() {
        "number-systems" => true,
        // A ∖ B holds what A does; A ∩ B what either does.
        "set-operations" => match (&*s.spelling().text(), s.children.as_slice()) {
            ("∖", [a, _]) => set_of_numbers(a),
            ("∩", [a, b]) => set_of_numbers(a) || set_of_numbers(b),
            (_, parts) => parts.iter().all(set_of_numbers),
        },
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
        Form::Set(name) | Form::Element(name) | Form::Property { name, .. }
            if rec
                .sorts
                .get(&name)
                .is_some_and(|s| super::sets::set_letter_type(s).is_some()) =>
        {
            true
        }
        // An element a line puts in a set of numbers, A ∈ ℝ ∖ ℚ, is a number
        // of that set's type (`theorem::element_number_type`).
        Form::Element(name) => {
            rec.page.entries().flat_map(|(_, n)| n.walk()).any(|n| {
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
    // A let naming a quotient as a whole number, `let e = p/d, a positive
    // integer`: the writer types the name by its kind and writes the value
    // in it, and a quotient is no integer to Lean until the reason's
    // witness is taken (`theorem::define`).
    if kinded_quotient(thm, rec) {
        return Covered::Out {
            reason: "a let names a quotient as a whole number, which the writer takes in its kind's type"
                .to_string(),
        };
    }
    // A set of naturals a define builds, S = {t ∈ ℕ : …}, is Lean's
    // `Set ℕ`, which no integer is a member of.
    if integer_in_natural_set(thm, rec) {
        return Covered::Out {
            reason: "an integer is said to be in a set of naturals a define builds, which Lean's Set ℕ does not hold"
                .to_string(),
        };
    }
    // The set-image item's map has one type (`items`), and {9ⁿ : n ∈ ℤ}
    // gives rationals of an integer index.
    if image_of_powers_cited(thm, rec) {
        return Covered::Out {
            reason: "a set-image of powers over ℤ cited through the set-image item, whose map takes one type"
                .to_string(),
        };
    }
    // A count of a set is in ℕ∞ (`sets::count_term`), whose subtraction
    // stops at 0 where the page's does not: |A| − |B| is not written.
    let count_subtracted =
        rec.page
            .entries()
            .flat_map(|(_, node)| node.walk())
            .any(|n| {
                let arithmetic =
                    matches!(&*n.notation_name(), "additive" | "multiplicative");
                let plus_or_times = matches!(&*n.spelling().text(), "+" | "·");
                arithmetic && !plus_or_times && super::expr::Writer::counts(&n)
            });
    if count_subtracted {
        return Covered::Out {
            reason: "a count of a set subtracted or divided, which ℕ∞ does not compute as the page does"
                .to_string(),
        };
    }
    // A citation that gives a count for a letter of a number system, m :=
    // |A| for m ∈ ℕ₀: the count is in ℕ∞, the letter in Lean's ℕ, and they
    // meet only through A being finite, which the writer does not carry.
    let count_given = rec
        .cited
        .iter()
        .flatten()
        .chain(rec.cited_requires.values())
        .any(|c| c.binding.values().any(super::expr::Writer::counts));
    if count_given {
        return Covered::Out {
            reason: "a count given for a number letter of a cited item, which Lean's ℕ meets in ℕ∞ only through finiteness"
                .to_string(),
        };
    }
    // A set-image over the page's ℕ or ℕ₀, {p·n : n ∈ ℕ}, or a map from it
    // said one-to-one or onto, f : ℕ → ℤ, maps Lean's ℕ into ℤ, and the map
    // items take one type in and out, α → α.
    let naturals = |set: &crate::formula::Node| {
        matches!(
            super::expr::system_of(set),
            Some(super::expr::System::Positive | super::expr::System::NonNegative)
        )
    };
    let from_naturals = rec
        .page
        .entries()
        .flat_map(|(_, node)| node.walk())
        .any(|n| match &*n.notation_name() {
            "set-image" => n.children.get(2).is_some_and(naturals),
            "one-to-one" | "onto" | "one-to-one-onto" => {
                n.children.get(1).is_some_and(naturals)
            }
            _ => false,
        });
    if from_naturals {
        return Covered::Out {
            reason: "a map from ℕ, Lean's ℕ into ℤ, where the map items take one type"
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
    // the statement (`theorem::header_recursions`).
    for line in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
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
            if &*n.notation_name() == "function-on" {
                let typed = matches!(n.children.as_slice(), [_, set]
                    if set_of_numbers(set)
                        || set.notation() == crate::notations::INTEGER_RANGE
                        || set.sort.full().and_then(super::expr::Members::of_set).is_some());
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
                        s.sort.full().and_then(super::expr::Members::of_set).is_some()
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
                Some(crate::formula::Whole::Set(m)) => {
                    matches!(**m, crate::formula::Whole::Number)
                        && among_numbers(&n.text, rec)
                }
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
