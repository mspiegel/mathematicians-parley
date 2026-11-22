//! The checker's record of a theorem, printed in the page's notation, one
//! decision to a line (`checker::record`): what each block owes, which item
//! a citation reads in which group and under what binding, which way each
//! conclusion is read and where each fact is taken from, which sums are said
//! once, and which relation each line a chain cites gives it. Everything is
//! placed by step number, never by the line of the file it is on, so a
//! rewrite that moves lines leaves the print as it was.

use std::fmt::Write as _;
use std::slice;

use parley::checker::record::{
    Cited, DomainSaid, Facing, FirstAt, OrderFact, OrderPart, Restated, SuppliedBy,
    Unfolded,
};
use parley::checker::CheckedCorpus;
use parley::citing::finite::{FiniteBy, Making};
use parley::corpus::proof::chain_reasons;
use parley::corpus::Theorem;
use parley::formula::Grammar;
use parley::matching::Meeting;

/// What a rewrite of requires lines changes in the record, by the place of
/// each requires line, `requires line 1 of step 2`.
pub struct RequiresRewrite<'a> {
    /// The requires lines whose own citation the record leaves out: the line
    /// may be read under another binding that fits it as well.
    pub omitted: &'a dyn Fn(&str) -> bool,
    /// The requires lines turned round, so that an order step restating the
    /// fact a line cites is recorded as reading it the other way round
    /// (`OrderRestated::turned`).
    pub flipped: &'a dyn Fn(&str) -> bool,
}

/// The record of the theorem `name` in `read`, as `rewrite` leaves it: with
/// the citation of each requires line it `omitted` left out, and the facing
/// of each fact an order step restates read the other way round where the
/// requires line was `flipped`.
pub fn printed_but(
    read: &CheckedCorpus,
    name: &str,
    rewrite: &RequiresRewrite<'_>,
) -> String {
    let RequiresRewrite { omitted, flipped } = *rewrite;
    let thm = read
        .corpus
        .theorems
        .iter()
        .find(|t| t.qualified() == name)
        .unwrap_or_else(|| panic!("no theorem {name}"));
    let record = read
        .theorems
        .get(name)
        .unwrap_or_else(|| panic!("the checker has no record of {name}"));
    let g: &Grammar = &read.grammar;
    let number = |i: usize| thm.steps[i].number.to_string();
    let mut out = format!("theorem {name}\n");
    for p in &record.problems {
        writeln!(out, "problem {}", p.message).unwrap();
    }
    for block in &record.blocks {
        let children: Vec<String> = block.children.iter().map(|&c| number(c)).collect();
        writeln!(
            out,
            "block of {}: {}",
            number(block.owner),
            children.join(", ")
        )
        .unwrap();
        for owed in &block.owes {
            let claim: Vec<String> = owed.claim.iter().map(|c| g.print(c)).collect();
            let part = owed
                .part
                .map_or("the block".to_string(), |p| format!("part {p}"));
            writeln!(out, "  {part} owes {}", claim.join(". ")).unwrap();
        }
    }
    // Whether the requires line at place `k` of the step numbered `step` is
    // one the rewrite changed.
    let rewritten_in = |step: String| {
        move |k: usize| omitted(&format!("requires line {} of step {step}", k + 1))
    };
    for (i, cited) in record.cited.iter().enumerate() {
        let Some(cited) = cited else { continue };
        let rewritten = rewritten_in(number(i));
        writeln!(out, "step {} {}", number(i), citation(cited, g, &rewritten)).unwrap();
    }
    for (line, cited) in &record.cited_requires {
        let at = requires_at(thm, *line);
        if !omitted(&at) {
            // The step whose requires lines the citation reads, as
            // `citations::requires_cited` files it: the step a requires
            // line is of, or whose calculation row's reason it is. The
            // citation of a `let` line's reason reads the let's own, which
            // name no step.
            let owner = thm
                .steps
                .iter()
                .find(|s| {
                    s.requires.iter().any(|r| r.line == *line)
                        || chain_reasons(&s.just, &thm.path)
                            .iter()
                            .any(|r| r.line == *line)
                })
                .map(|s| s.number.to_string());
            let printed = match owner {
                Some(step) => citation(cited, g, &rewritten_in(step)),
                None => citation(cited, g, &|_| false),
            };
            writeln!(out, "{at} {printed}").unwrap();
        }
    }
    for (i, sums) in record.said_sums.iter().enumerate() {
        for sum in sums {
            writeln!(
                out,
                "step {} says once {} is a number",
                number(i),
                g.print(sum)
            )
            .unwrap();
        }
    }
    for (set, why) in &record.said_finite.sets {
        writeln!(out, "finite {}, by {}", g.print(&set.0), finite_why(why, g)).unwrap();
    }
    for (line, only) in &record.said_finite.only_by {
        let only: Vec<String> = only.iter().map(|s| g.print(&s.0)).collect();
        writeln!(
            out,
            "only {} makes finite {}",
            g.print(&line.0),
            only.join(", ")
        )
        .unwrap();
    }
    for (set, system) in &record.set_systems {
        writeln!(out, "set {set} holds numbers of {}", system.label()).unwrap();
    }
    for (line, chain) in &record.links {
        let at = thm
            .steps
            .iter()
            .find(|s| s.just.line == *line)
            .map_or_else(|| format!("line {line}"), |s| format!("step {}", s.number));
        // Each link, where it stands, and whether the chain reads it turned.
        let links: Vec<String> = chain
            .links
            .iter()
            .map(|l| {
                let at =
                    l.at.as_ref()
                        .map_or_else(|| "no line".to_string(), order_fact);
                let turned = if l.turned { ", turned" } else { "" };
                format!("{} ({at}{turned})", g.print(&l.said))
            })
            .collect();
        let claim = if chain.claim_turned {
            ", the claim turned"
        } else {
            ""
        };
        writeln!(out, "{at} chains {}{claim}", links.join(" | ")).unwrap();
    }
    for (line, values) in &record.exhibited {
        let at = thm
            .steps
            .iter()
            .find(|s| s.just.line == *line)
            .map_or_else(|| format!("line {line}"), |s| format!("step {}", s.number));
        for (i, value) in values.iter().enumerate() {
            let shown = match value {
                Some(at) => {
                    let values = at
                        .values
                        .iter()
                        .map(|(letter, v)| format!("{letter} := {}", g.print(v)))
                        .collect::<Vec<_>>()
                        .join(", ");
                    let by: Vec<String> =
                        at.shown.iter().map(|s| supplier(&s.by)).collect();
                    format!("{values}; facts by {}", by.join(", "))
                }
                None => "no value".to_string(),
            };
            writeln!(out, "{at} exhibits in sentence {i} {shown}").unwrap();
        }
    }
    // Where a justification stands: a step's own, or a row or requires line
    // inside one, by the step.
    let reason_at = |line: usize| {
        thm.steps
            .iter()
            .find(|s| s.just.line == line)
            .map(|s| format!("step {}", s.number))
            .or_else(|| {
                thm.steps
                    .iter()
                    .find(|s| s.requires.iter().any(|r| r.line == line))
                    .map(|_| requires_at(thm, line))
            })
            .unwrap_or_else(|| {
                let owner = thm
                    .steps
                    .iter()
                    .rev()
                    .find(|s| s.just.line < line)
                    .map_or("the theorem".to_string(), |s| {
                        format!("step {}", s.number)
                    });
                format!("a row of {owner}")
            })
    };
    for (line, inst) in &record.instantiated {
        let conditions: Vec<String> =
            inst.conditions.iter().map(|c| supplier(&c.by)).collect();
        let guards: Vec<String> = inst
            .guards
            .iter()
            .map(|g| format!("{} by {}", g.letter, supplier(&g.by)))
            .collect();
        writeln!(
            out,
            "{} instantiates {}, conditions taken off [{}], guards [{}]",
            reason_at(*line),
            place(&inst.at),
            conditions.join(", "),
            guards.join(", ")
        )
        .unwrap();
    }
    for (line, member) in &record.at_member {
        let over = if member.part {
            "parts of"
        } else {
            "members of"
        };
        writeln!(
            out,
            "{} is read at {}, over the {over} {}",
            reason_at(*line),
            member.letter,
            g.print(&member.set)
        )
        .unwrap();
    }
    for (line, at) in &record.link_places {
        writeln!(out, "{} links from {}", reason_at(*line), place(at)).unwrap();
    }
    for (line, restated) in &record.restated {
        if let Restated::Stated { at, .. } | Restated::UnderClaim { at, .. } = restated
        {
            writeln!(out, "{} restates {}", reason_at(*line), place(at)).unwrap();
        }
    }
    for (line, order) in &record.orders {
        for (k, parts) in order.sentences.iter().enumerate() {
            for (j, part) in parts.iter().enumerate() {
                writeln!(
                    out,
                    "{} sentence {k} part {j} {}",
                    reason_at(*line),
                    order_part(part, flipped(&reason_at(*line)))
                )
                .unwrap();
            }
        }
    }
    for (line, sentences) in &record.joined {
        for (k, parts) in sentences.iter().enumerate() {
            let at: Vec<String> = parts.iter().map(place).collect();
            writeln!(
                out,
                "{} joins in sentence {k} [{}]",
                reason_at(*line),
                at.join(", ")
            )
            .unwrap();
        }
    }
    for (line, a) in &record.antisymmetric {
        writeln!(
            out,
            "{} antisymmetric from {} and {}",
            reason_at(*line),
            place(&a.below),
            place(&a.above)
        )
        .unwrap();
    }
    for (line, facing) in &record.link_facings {
        writeln!(
            out,
            "{} links facing {}",
            reason_at(*line),
            facing_word(*facing)
        )
        .unwrap();
    }
    for (line, s) in &record.substituted {
        if let Some(facing) = s.define_facing {
            writeln!(
                out,
                "{} takes {} from a define, facing {}",
                reason_at(*line),
                g.print(&s.equation),
                facing_word(Some(facing))
            )
            .unwrap();
        }
    }
    for (line, applied) in &record.define_domains {
        for one in applied {
            let by = match &one.said {
                DomainSaid::Line(at) => place(at),
                DomainSaid::Member => "the claim's member".to_string(),
                DomainSaid::SumRange => "the sum's range".to_string(),
                DomainSaid::LimitIndex => "the sequence's index".to_string(),
            };
            writeln!(
                out,
                "{} has its define's argument in the domain by {by}",
                reason_at(*line)
            )
            .unwrap();
        }
    }
    for (line, parts) in &record.obtained_parts {
        let pairs: Vec<String> = parts
            .iter()
            .map(|p| {
                format!("sentence {} part {} is part {}", p.sentence, p.part, p.owed)
            })
            .collect();
        writeln!(out, "{} obtains {}", reason_at(*line), pairs.join(", ")).unwrap();
    }
    for (line, at) in &record.obtained_from {
        writeln!(out, "{} obtains from {}", reason_at(*line), place(at)).unwrap();
    }
    out
}

/// The requires line on `line`, by its step and its place among the step's
/// requires lines.
pub fn requires_at(thm: &Theorem, line: usize) -> String {
    for step in &thm.steps {
        if let Some(k) = step.requires.iter().position(|r| r.line == line) {
            return format!("requires line {} of step {}", k + 1, step.number);
        }
    }
    format!("requires line on line {line}")
}

/// A citation as the record holds it: the item and group, its binding,
/// each conclusion and the way it is read, and where each fact is taken.
/// Why a set is finite, each line and set printed as the page writes it.
fn finite_why(why: &FiniteBy, g: &Grammar) -> String {
    match why {
        FiniteBy::Said(line) => format!("Said({:?})", g.print(&line.0)),
        FiniteBy::Counted { line, at_least_one } => format!(
            "Counted {{ line: {:?}, at_least_one: {at_least_one} }}",
            g.print(&line.0)
        ),
        FiniteBy::Part { line, whole } => format!(
            "Part {{ line: {:?}, whole: {} }}",
            g.print(&line.0),
            finite_why(whole, g)
        ),
        FiniteBy::Covered { line, over } => format!(
            "Covered {{ line: {:?}, over: {} }}",
            g.print(&line.0),
            finite_why(over, g)
        ),
        FiniteBy::Define(name) => format!("Define({name:?})"),
        FiniteBy::Bound(name) => format!("Bound({name:?})"),
        FiniteBy::MemberOf(whole) => format!("MemberOf({})", finite_why(whole, g)),
        FiniteBy::Made(made) => format!("Made({})", making(made, g)),
    }
}

/// How a finite set is made, its parts' reasons printed by `finite_why`.
fn making(made: &Making, g: &Grammar) -> String {
    match made {
        Making::Empty => "Empty".to_string(),
        Making::Listed => "Listed".to_string(),
        Making::Range => "Range".to_string(),
        Making::Minus(a) => format!("Minus({})", finite_why(a, g)),
        Making::Inter(a) => format!("Inter({})", finite_why(a, g)),
        Making::Union(a, b) => {
            format!("Union({}, {})", finite_why(a, g), finite_why(b, g))
        }
        Making::Powerset(a) => format!("Powerset({})", finite_why(a, g)),
        Making::Builder(a) => format!("Builder({})", finite_why(a, g)),
        Making::Image(a) => format!("Image({})", finite_why(a, g)),
        Making::Coset(a) => format!("Coset({})", finite_why(a, g)),
        Making::Applied(name) => format!("Applied({name:?})"),
        Making::Functions(a, b) => {
            format!("Functions({}, {})", finite_why(a, g), finite_why(b, g))
        }
        Making::Product(a, b) => {
            format!("Product({}, {})", finite_why(a, g), finite_why(b, g))
        }
    }
}

/// A citation in one line. `rewritten` says whether the requires line at
/// that place among the citing step's is one a rewrite changed, whose
/// meeting with what it supplies is not compared.
fn citation(cited: &Cited, g: &Grammar, rewritten: &dyn Fn(usize) -> bool) -> String {
    // A binding says what each letter stands for, in no order.
    let mut binding: Vec<String> = cited
        .binding
        .iter()
        .map(|(k, v)| format!("{k} := {}", g.print(v)))
        .collect();
    binding.sort();
    let mut bound: Vec<String> = cited
        .bound
        .iter()
        .map(|(k, v)| format!("{k} := {}", g.print(v)))
        .collect();
    bound.sort();
    if !bound.is_empty() {
        binding.push(format!("bound {}", bound.join(", ")));
    }
    let concluded: Vec<String> = cited
        .concluded
        .iter()
        .map(|c| match c.part {
            Some(p) => format!("{} {:?} part {p}", c.sentence, c.way),
            None => format!("{} {:?}", c.sentence, c.way),
        })
        .collect();
    // Each line read from, and how it met what the reading asks first
    // where it took anything (`Cited::firsts_meetings`).
    let firsts: Vec<String> = cited
        .firsts
        .iter()
        .enumerate()
        .map(
            |(k, by)| match cited.firsts_meetings.get(k).cloned().flatten() {
                Some(m) if !m.as_written() => {
                    format!("{} met {}", supplier(by), meeting_words(&m))
                }
                _ => supplier(by),
            },
        )
        .collect();
    let from = if firsts.is_empty() {
        "no line".to_string()
    } else {
        firsts.join(", ")
    };
    // Each by where the item writes it: hypothesis line, then sentence,
    // each from 1; with how the fact met it where that took anything, and
    // the set a "for all" was narrowed to.
    let supplied: Vec<String> = cited
        .supplied
        .iter()
        .map(|s| {
            let mut said = match s.at {
                Some(at) => {
                    format!("{}.{} {}", at.line + 1, at.sentence + 1, supplier(&s.by))
                }
                None => supplier(&s.by),
            };
            // How a requires line the rewrite changed meets is left out, as
            // that line's own citation is (`RequiresRewrite::omitted`).
            let changed =
                matches!(s.by, SuppliedBy::Requires { line, .. } if rewritten(line));
            if let Some(m) = s.meeting.as_ref().filter(|m| !m.as_written() && !changed)
            {
                write!(said, " met {}", meeting_words(m)).unwrap();
            }
            if let Some(n) = &s.narrowed {
                write!(said, " narrowed to {}", g.print(&n.to)).unwrap();
            }
            said
        })
        .collect();
    // Each letter's number systems, the item's then its value's, in no
    // order.
    let mut letters: Vec<String> = cited
        .item_letters
        .iter()
        .map(|l| {
            let item = l.item_system.map_or("none", |s| s.label());
            let value = l.value_system.map_or("none", |s| s.label());
            match l.value_set {
                Some(set) => {
                    format!("{} {item} from {value}, the set {}", l.letter, set.label())
                }
                None => format!("{} {item} from {value}", l.letter),
            }
        })
        .collect();
    letters.sort();
    let facings: Vec<&str> = cited.facings.iter().map(|f| facing_word(*f)).collect();
    // Which part of a property's body each claim sentence is, where one is.
    let within = match cited.within.iter().any(Option::is_some) {
        true => {
            let parts: Vec<String> = cited
                .within
                .iter()
                .map(|w| w.map_or("whole".to_string(), |j| format!("part {j}")))
                .collect();
            format!("; within {}", parts.join(", "))
        }
        false => String::new(),
    };
    // How each conclusion met the claim's sentence: as written, or what the
    // meeting took to meet them; apart where they did not meet as wholes.
    let met: Vec<String> = cited
        .meetings
        .iter()
        .map(|m| match m {
            None => "apart".to_string(),
            Some(m) => meeting_words(m),
        })
        .collect();
    // What a definition read backwards asks of its right side, where one is.
    let unfolded = match cited.unfolded.iter().any(Option::is_some) {
        true => {
            let each: Vec<String> = cited
                .unfolded
                .iter()
                .map(|u| match u {
                    None => "none".to_string(),
                    Some(parts) => format!("[{}]", unfolded_parts(parts, g)),
                })
                .collect();
            format!("; unfolded {}", each.join(", "))
        }
        false => String::new(),
    };
    // The sentence an obtain takes its "there is" from, counted across the
    // item's groups.
    let obtained = cited
        .obtained
        .map_or(String::new(), |k| format!("; obtains sentence {k}"));
    format!(
        "cites {} group {}; {}; concludes {}{obtained}; from {from}; supplied by {}; letters {}; facing {}; met {}{within}{unfolded}",
        cited.item,
        cited.group,
        binding.join(", "),
        concluded.join(", "),
        supplied.join(", "),
        letters.join(", "),
        facings.join(", "),
        met.join(", "),
    )
}

/// What a meeting took to meet two trees, in words; "as written" where it
/// took nothing.
fn meeting_words(m: &Meeting) -> String {
    let mut took: Vec<&str> = Vec::new();
    for (flag, word) in [
        (m.turned, "turned"),
        (m.permuted, "permuted"),
        (m.renamed, "renamed"),
        (m.respelled, "respelled"),
        (!m.unfolded.is_empty(), "defines read out"),
        (!m.identities.is_empty(), "identities dropped"),
        (!m.flips.is_empty(), "flipped"),
    ] {
        if flag {
            took.push(word);
        }
    }
    match took.is_empty() {
        true => "as written".to_string(),
        false => took.join(" and "),
    }
}

/// The parts of a definition's right side (`Cited::unfolded`): each fact
/// and what supplies it, each witness with its membership and its body's
/// parts.
fn unfolded_parts(parts: &[Unfolded], g: &Grammar) -> String {
    let each: Vec<String> = parts
        .iter()
        .map(|p| match p {
            Unfolded::Fact { fact, by } => {
                format!("{} by {}", g.print(fact), supplier(by))
            }
            Unfolded::Witness {
                value,
                member,
                body,
            } => format!(
                "witness {} with {}; {}",
                g.print(value),
                unfolded_parts(slice::from_ref(member.as_ref()), g),
                unfolded_parts(body, g)
            ),
        })
        .collect();
    each.join(", ")
}

/// Which way an equation or congruence faces another, in a word.
fn facing_word(facing: Option<Facing>) -> &'static str {
    match facing {
        Some(Facing::Straight) => "straight",
        Some(Facing::Turned) => "turned",
        None => "none",
    }
}

/// Where a fact stands in a line, by its sentence and part, and the rule
/// where the line implies it (`record::FirstAt`).
pub fn place(f: &FirstAt) -> String {
    let mut at = f.line.clone();
    if let Some(s) = f.sentence {
        write!(at, " sentence {s}").unwrap();
    }
    if let Some(p) = f.part {
        write!(at, " part {p}").unwrap();
    }
    if let Some(rule) = f.implied {
        write!(at, " implied by {rule:?}").unwrap();
    }
    at
}

/// What one part of an order step rests on (`record::OrderPart`).
fn order_part(part: &OrderPart, flipped: bool) -> String {
    let facts = |of: &[OrderFact]| -> String {
        of.iter().map(order_fact).collect::<Vec<_>>().join(", ")
    };
    let mut said = match &part.restates {
        Some(r) => format!(
            "restates {}{}",
            order_fact(&r.by),
            if r.turned != flipped { ", turned" } else { "" }
        ),
        None => format!("adds [{}]", facts(&part.uses)),
    };
    if !part.split.is_empty() {
        write!(said, " split on [{}]", facts(&part.split)).unwrap();
    }
    if let Some(w) = part.weakened {
        write!(said, " weakened from {w:?}").unwrap();
    }
    said
}

/// Where a fact an order step adds stands (`record::OrderFact`).
fn order_fact(fact: &OrderFact) -> String {
    match fact {
        OrderFact::Line(at) => place(at),
        OrderFact::Define(label) => format!("define {label}"),
        OrderFact::Kind {
            define, implied, ..
        } => format!("kind of {define} implied by {implied:?}"),
        OrderFact::Requires { line, implied } => match implied {
            Some(rule) => format!("requires {} implied by {rule:?}", line + 1),
            None => format!("requires {}", line + 1),
        },
        OrderFact::Member { implied, .. } => format!("member implied by {implied:?}"),
    }
}

/// What supplies a hypothesis (`record::SuppliedBy`).
fn supplier(by: &SuppliedBy) -> String {
    match by {
        SuppliedBy::Line(at) => place(at),
        SuppliedBy::SaidOnce(at) => format!("once {}", place(at)),
        SuppliedBy::Requires { line, implied } => match implied {
            Some(rule) => format!("requires {} implied by {rule:?}", line + 1),
            None => format!("requires {}", line + 1),
        },
        SuppliedBy::Walked(walked) => format!("walked {:?}", walked.reason),
        SuppliedBy::Through { carrier, member } => {
            format!("through {} and {}", supplier(carrier), supplier(member))
        }
        SuppliedBy::Bound { letter } => format!("bound {letter}"),
        SuppliedBy::Identity(met) => format!("identity {met:?}"),
        SuppliedBy::Parts(parts) => format!(
            "parts [{}]",
            parts.iter().map(supplier).collect::<Vec<_>>().join("; ")
        ),
        SuppliedBy::Unstated => "unstated".to_string(),
    }
}
