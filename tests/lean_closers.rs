//! Each closer rule of the Lean writer at a step it decides, and beside it a
//! step where its Lean fact says it does not hold, which keeps its ways
//! (`docs/LEAN.md`, how a line proves a statement; `src/lean/casts.rs`).
//!
//! The Lean build proves every step; this test says which tactic each rule
//! chose where, so that a change to a rule's fact, or to how the writer
//! reads it, shows here by name and not only as a proof that still passes
//! by another way.

use std::path::Path;

/// One step of a generated Lean file, and what its proof is.
struct Site {
    file: &'static str,
    step: &'static str,
    /// Text the step's proof holds: the tactic the rule chose.
    holds: &'static str,
    /// Whether the line holding it is a `first` list, as one no rule
    /// decides is.
    list: bool,
    /// The rule, and why it holds or does not here.
    why: &'static str,
}

const SITES: &[Site] = &[
    Site {
        file: "lean/Parley/Proofs/Wiedijk/Harmonic/HarmonicBlock.lean",
        step: "14",
        holds: "exact_mod_cast",
        list: false,
        why: "a citation alike but for casts, every cast one norm_cast moves (Σ, /, ^): exact_mod_cast",
    },
    Site {
        file: "lean/Parley/Tests/Stdlib/Numbers/AbsNonneg.lean",
        step: "1",
        holds: "exact_mod_cast",
        list: false,
        why: "a citation the writer's comparison does not meet, ‖(x : ℂ)‖ beside |x|, whose forms as norm_cast leaves them are alike: exact_mod_cast",
    },
    Site {
        file: "lean/Parley/Proofs/Setmm/ChooseOneLess/ChooseOneLess.lean",
        step: "1",
        holds: "simpa only [Int.cast_id, exists_eq_right]",
        list: false,
        why: "a definition over any ring taken at ℤ, ∃ m : ℤ, 0 < m ∧ (m : ℤ) = N beside the writer's 0 < N: Int.cast_id and exists_eq_right",
    },
    Site {
        file: "lean/Parley/Proofs/Setmm/LimitAddConstant/LimitAddConstant.lean",
        step: "2",
        holds: ".mpr s1",
        list: false,
        why: "a definition read backwards whose left side is the claim up to what Lean takes as one term, (fun n => x n + C) n beside x n + C: the reading as a term",
    },
    Site {
        file: "lean/Parley/Tests/Notations/Powers/EToARealPower.lean",
        step: "1",
        holds: "first |",
        list: true,
        why: "a citation whose cast stands under a complex power e ^ y, which norm_cast does not move: no one tactic",
    },
    Site {
        file: "lean/Parley/Tests/Notations/Numbers/SqrtFourNotIrrational.lean",
        step: "3",
        holds: "push_cast at",
        list: false,
        why: "casts push_cast moves and norm_cast does not, in one type: push_cast at h ⊢; exact h",
    },
    Site {
        file: "lean/Parley/Proofs/Setmm/Parity/OddSquareOverEight.lean",
        step: "1",
        holds: "first |",
        list: true,
        why: "casts neither tactic is known to move: the ways tried in order",
    },
    Site {
        file: "lean/Parley/Proofs/Hammack/FibonacciSum/FibonacciSum.lean",
        step: "5",
        holds: "linear_combination",
        list: false,
        why: "an instance equation of numbers whose casts push_cast moves, in the claim's type: linear_combination, whose parley_norm checks push_cast; ring1",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/RealsUncountable/DecimalNumber.lean",
        step: "5.4",
        holds: "linarith [",
        list: false,
        why: "an instance order with the claim's casts, over the same atoms: linarith",
    },
    Site {
        file: "lean/Parley/Proofs/Hammack/SumOfCubes/SumOfCubes.lean",
        step: "1.1",
        holds: "linear_combination",
        list: false,
        why: "a calculation row citing an item's equation in the row's type, (fun j => (j : ℚ) ^ 3) 1 beside 1 ^ 3: casts push_cast moves within each side, the same atoms, facing known: linear_combination",
    },
    Site {
        file: "lean/Parley/Proofs/Setmm/EmptySum/EmptySum.lean",
        step: "2",
        holds: "first |",
        list: true,
        why: "an item's equation whose atoms differ inside, ∑ over Icc (0 + 1) 0 beside Icc 1 0, which ring1 does not work in: no one tactic",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/PrimeFactorisation/PrimeTimesProduct.lean",
        step: "12",
        holds: ".symm",
        list: false,
        why: "an item's equation the checker met turned round, ∏ i beside ∏ k (Cited::facings): linear_combination of its symm",
    },
    Site {
        file: "lean/Parley/Proofs/Setmm/ConstantFunctionContinuous/ConstantFunctionContinuous.lean",
        step: "1.1.1.1",
        holds: "first |",
        list: true,
        why: "an instance Lean states otherwise than the claim, by no fact a closer rests on: the ways tried in order",
    },
];

/// The lines of the step `step` in `text`: from its comment to the next
/// step's.
fn step_lines<'t>(text: &'t str, step: &str) -> Option<Vec<&'t str>> {
    let opens = |line: &str| {
        line.trim_start()
            .strip_prefix("-- ")
            .and_then(|c| c.split_once(". "))
            .map(|(n, _)| n.to_string())
    };
    let mut lines = text
        .lines()
        .skip_while(|l| opens(l).as_deref() != Some(step));
    let first = lines.next()?;
    let mut out = vec![first];
    out.extend(
        lines.take_while(|l| {
            opens(l).is_none_or(|n| n.starts_with(&format!("{step}.")))
        }),
    );
    Some(out)
}

#[test]
fn each_closer_rule_decides_where_its_fact_holds() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut wrong = Vec::new();
    for site in SITES {
        let text = std::fs::read_to_string(root.join(site.file))
            .unwrap_or_else(|_| panic!("{} is written", site.file));
        let Some(lines) = step_lines(&text, site.step) else {
            wrong.push(format!("{} has no step {}", site.file, site.step));
            continue;
        };
        // The step's own lines, a block's inner steps left out.
        let inner = format!("-- {}.", site.step);
        let own: Vec<&str> = lines
            .iter()
            .copied()
            .skip(1)
            .take_while(|l| !l.trim_start().starts_with(&inner))
            .collect();
        let body = own.join("\n");
        // The line the rule wrote, and whether it is a list: a block's
        // close after it is another line's.
        let line = own.iter().find(|l| l.contains(site.holds));
        let listed = line.is_some_and(|l| l.contains("first |"));
        if line.is_none() || listed != site.list {
            wrong.push(format!(
                "{} step {}: {}\n  wanted {} {}; the step reads:\n{}",
                site.file,
                site.step,
                site.why,
                site.holds,
                if site.list { "in a list" } else { "alone" },
                body
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n\n"));
}
