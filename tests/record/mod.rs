//! The checker's record of a theorem, printed in the page's notation, one
//! decision to a line (`checker::record`): what each block owes, which item
//! a citation reads in which group and under what binding, which way each
//! conclusion is read and where each fact is taken from, which sums are said
//! once, and which relation each line a chain cites gives it. Everything is
//! placed by step number, never by the line of the file it is on, so a
//! rewrite that moves lines leaves the print as it was.

use std::fmt::Write as _;

use parley::checker::record::Cited;
use parley::checker::CheckedCorpus;
use parley::corpus::Theorem;
use parley::formula::Grammar;

/// The record of the theorem `name` in `read`, leaving out the citation of
/// each requires line `omitted` names, `requires line 1 of step 2`.
pub fn printed_but(
    read: &CheckedCorpus,
    name: &str,
    omitted: &dyn Fn(&str) -> bool,
) -> String {
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
    for (i, cited) in record.cited.iter().enumerate() {
        let Some(cited) = cited else { continue };
        writeln!(out, "step {} {}", number(i), citation(cited, g)).unwrap();
    }
    for (line, cited) in &record.cited_requires {
        let at = requires_at(thm, *line);
        if !omitted(&at) {
            writeln!(out, "{at} {}", citation(cited, g)).unwrap();
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
        writeln!(out, "finite {set}, by {why:?}").unwrap();
    }
    for (line, only) in &record.said_finite.only_by {
        let only: Vec<&str> = only.iter().map(String::as_str).collect();
        writeln!(out, "only {line} makes finite {}", only.join(", ")).unwrap();
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
    for (line, at) in &record.link_places {
        writeln!(out, "{} links from {}", reason_at(*line), place(at)).unwrap();
    }
    for (line, at) in &record.restated {
        writeln!(out, "{} restates {}", reason_at(*line), place(at)).unwrap();
    }
    for (line, order) in &record.orders {
        for (k, parts) in order.sentences.iter().enumerate() {
            for (j, part) in parts.iter().enumerate() {
                writeln!(
                    out,
                    "{} sentence {k} part {j} {}",
                    reason_at(*line),
                    order_part(part)
                )
                .unwrap();
            }
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
            facing_word(Some(*facing))
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
    for (line, said) in &record.define_domains {
        let by = match said {
            parley::checker::record::DomainSaid::Line(at) => place(at),
            parley::checker::record::DomainSaid::Member => {
                "the claim's member".to_string()
            }
        };
        writeln!(
            out,
            "{} has its define's argument in the domain by {by}",
            reason_at(*line)
        )
        .unwrap();
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
fn citation(cited: &Cited, g: &Grammar) -> String {
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
        .map(|c| format!("{} {:?}", c.sentence, c.way))
        .collect();
    let firsts: Vec<String> = cited.firsts.iter().map(place).collect();
    let from = if firsts.is_empty() {
        "no line".to_string()
    } else {
        firsts.join(", ")
    };
    let supplied: Vec<String> =
        cited.supplied.iter().map(|s| supplier(&s.by)).collect();
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
            Some(m) => {
                let mut took: Vec<&str> = Vec::new();
                for (flag, word) in [
                    (m.turned, "turned"),
                    (m.permuted, "permuted"),
                    (m.renamed, "renamed"),
                    (m.respelled, "respelled"),
                    (!m.identities.is_empty(), "identities dropped"),
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
    format!(
        "cites {} group {}; {}; concludes {}; from {from}; supplied by {}; letters {}; facing {}; met {}{within}{unfolded}",
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

/// The parts of a definition's right side (`Cited::unfolded`): each fact
/// and what supplies it, each witness with its membership and its body's
/// parts.
fn unfolded_parts(parts: &[parley::checker::record::Unfolded], g: &Grammar) -> String {
    use parley::checker::record::Unfolded;
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
                unfolded_parts(std::slice::from_ref(member.as_ref()), g),
                unfolded_parts(body, g)
            ),
        })
        .collect();
    each.join(", ")
}

/// Which way an equation or congruence faces another, in a word.
fn facing_word(facing: Option<parley::checker::record::Facing>) -> &'static str {
    match facing {
        Some(parley::checker::record::Facing::Straight) => "straight",
        Some(parley::checker::record::Facing::Turned) => "turned",
        None => "none",
    }
}

/// Where a fact stands in a line, by its sentence and part, and the rule
/// where the line implies it (`record::FirstAt`).
pub fn place(f: &parley::checker::record::FirstAt) -> String {
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
fn order_part(part: &parley::checker::record::OrderPart) -> String {
    let facts = |of: &[parley::checker::record::OrderFact]| -> String {
        of.iter().map(order_fact).collect::<Vec<_>>().join(", ")
    };
    let mut said = match &part.restates {
        Some(r) => format!(
            "restates {}{}",
            order_fact(&r.by),
            if r.turned { ", turned" } else { "" }
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
fn order_fact(fact: &parley::checker::record::OrderFact) -> String {
    use parley::checker::record::OrderFact;
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
        OrderFact::Member(rule) => format!("member implied by {rule:?}"),
    }
}

/// What supplies a hypothesis (`record::SuppliedBy`).
fn supplier(by: &parley::checker::record::SuppliedBy) -> String {
    use parley::checker::record::SuppliedBy;
    match by {
        SuppliedBy::Line(at) => place(at),
        SuppliedBy::SaidOnce(at) => format!("once {}", place(at)),
        SuppliedBy::Requires { line, implied } => match implied {
            Some(rule) => format!("requires {} implied by {rule:?}", line + 1),
            None => format!("requires {}", line + 1),
        },
        SuppliedBy::Unstated => "unstated".to_string(),
    }
}
