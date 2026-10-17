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
    for (line, links) in &record.links {
        let at = thm
            .steps
            .iter()
            .find(|s| s.just.line == *line || s.line == *line)
            .map_or_else(|| format!("line {line}"), |s| format!("step {}", s.number));
        let links: Vec<String> = links.iter().map(|l| g.print(l)).collect();
        writeln!(out, "{at} chains {}", links.join(" | ")).unwrap();
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
    let concluded: Vec<String> = cited
        .concluded
        .iter()
        .map(|c| format!("{} {:?}", c.sentence, c.way))
        .collect();
    let firsts: Vec<String> = cited
        .firsts
        .iter()
        .map(|f| {
            let mut at = f.line.clone();
            if let Some(s) = f.sentence {
                write!(at, " sentence {s}").unwrap();
            }
            if let Some(p) = f.part {
                write!(at, " part {p}").unwrap();
            }
            at
        })
        .collect();
    let from = if firsts.is_empty() {
        "no line".to_string()
    } else {
        firsts.join(", ")
    };
    format!(
        "cites {} group {}; {}; concludes {}; from {from}",
        cited.item,
        cited.group,
        binding.join(", "),
        concluded.join(", "),
    )
}
