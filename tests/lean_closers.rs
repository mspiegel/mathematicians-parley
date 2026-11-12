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
        file: "lean/Parley/Proofs/Hammack/InverseSquareHasNoLimit/InverseSquareHasNoLimit.lean",
        step: "10.12",
        holds: "exact Eq.trans_lt hD1 s10_7",
        list: false,
        why: "a chain whose first link is a define's equation: the define's hypothesis, as the checker placed the link (`links`)",
    },
    Site {
        file: "lean/Parley/Proofs/Hammack/InverseSquareHasNoLimit/InverseSquareHasNoLimit.lean",
        step: "10.7",
        holds: "(show 1 / (j : ℝ) ≤ 1 / (m : ℝ) by exact_mod_cast s10_3)",
        list: false,
        why: "a chain's link in ℚ beside links in ℝ: taken up to ℝ by exact_mod_cast, its letters' casts read as ℤ to ℚ to ℝ",
    },
    Site {
        file: "lean/Parley/Proofs/Hammack/QuadraticOverLinearDiverges/QuadraticOverLinearDiverges.lean",
        step: "1.2.12",
        holds: "exact lt_trans s1_1b (show (n : ℝ) > (N : ℝ) by exact_mod_cast hA2)",
        list: false,
        why: "links the page writes with `>` and Lean states with `<`, read from the side Lean states them",
    },
    Site {
        file: "lean/Parley/Proofs/Setmm/NaturalAtMostSquare/NaturalAtMostSquare.lean",
        step: "4",
        holds: "linarith only [s2, s3]",
        list: false,
        why: "a chain the checker met only with an identity element dropped, n·1 beside n: linear arithmetic over its links",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/Harmonic/HarmonicUnbounded.lean",
        step: "5",
        holds: "by linarith only [s3b]",
        list: false,
        why: "rows from a line, each a linear move: linear arithmetic on the line the first row writes out, as the checker recorded it (`orders`)",
    },
    Site {
        file: "lean/Parley/Proofs/Setmm/FloorBelowNonInteger/FloorBelowNonInteger.lean",
        step: "4",
        holds: "exact Or.elim (Ne.lt_or_gt s3) (fun h1 => by linarith only [s1, h1]) (fun h1 => by linarith only [s1, h1])",
        list: false,
        why: "a disequality the combination takes both ways: split by Ne.lt_or_gt, each case linear arithmetic over the recorded facts",
    },
    Site {
        file: "lean/Parley/Proofs/Setmm/LimitUnique/LimitUnique.lean",
        step: "3",
        holds: "exact le_antisymm s1 s2",
        list: false,
        why: "antisymmetry: the line that says the claim's left side is at most its right, then the converse, as the checker paired them (`antisymmetric`)",
    },
    Site {
        file: "lean/Parley/Proofs/Setmm/RemainderBounds/RemainderNonnegative.lean",
        step: "1",
        holds: "ne_of_gt (by linarith only [hH3])",
        list: false,
        why: "rows ending in a weakening of `>` to `≠`: ne_of_gt of the order, linear arithmetic on the line",
    },
    Site {
        file: "lean/Parley/Proofs/Setmm/RemainderZero/NoRemainderIsWholeQuotient.lean",
        step: "3.4",
        holds: "(exact_mod_cast (Parley.Proofs.Setmm.FloorBasics.FloorOfInteger.floor_of_integer",
        list: false,
        why: "an item met as written through a named number the proof puts first, ⌊↑c⌋ = c beside the claim's ↑⌊↑c⌋ = ↑c: the item's equation cast up as a whole, which norm_cast takes back, exact_mod_cast",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/Wilson/Wilson.lean",
        step: "5.5.3",
        holds: "exact ⟨_, rfl, (Parley.Items.Stdlib.Sums.mun_range_from_bounds",
        list: false,
        why: "a range member Lean writes as the integer that is it, met as written through a named number: that number, rfl, and the item's membership",
    },
    Site {
        file: "lean/Parley/Tests/Stdlib/Sums/Range.lean",
        step: "1",
        holds: "exact ⟨⟨_, (h).1, rfl⟩, by exact_mod_cast (h).2⟩",
        list: false,
        why: "an \"and\" met as written, part by part: a membership of ℕ Lean writes as an integer of a real beside the item's 0 < c, and an order cast up",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/Harmonic/HarmonicBlock.lean",
        step: "14",
        holds: "by parley_instance (",
        list: false,
        why: "a citation whose item, at its values, the step's lines write otherwise than Lean states it, in one number type: read in the step's spelling, parley_instance",
    },
    Site {
        file: "lean/Parley/Tests/Stdlib/Numbers/AbsNonneg.lean",
        step: "1",
        holds: "by parley_instance_cast (",
        list: false,
        why: "an item in ℂ cited at a real, ‖(x : ℂ)‖ beside |x|: read in the step's spelling with its casts lifted out, parley_instance_cast",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/PrimeFactorisation/PrimeFactorisation.lean",
        step: "1.17",
        holds: "exact_mod_cast",
        list: false,
        why: "a citation the route leaves to the closer, alike but for casts, every cast one norm_cast moves: exact_mod_cast",
    },
    Site {
        file: "lean/Parley/Proofs/Setmm/ChooseOneLess/ChooseOneLess.lean",
        step: "1",
        holds: "by parley_instance (",
        list: false,
        why: "a definition over any ring taken at ℤ, ∃ m : ℤ, 0 < m ∧ (m : ℤ) = N, beside the writer's 0 < N: read in the step's spelling by parley_spelling's Int.cast_id and exists_eq_right, parley_instance",
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
        holds: "parley_of_complex h",
        list: false,
        why: "an item worked in ℂ, e ^ y at (y : ℂ), cited for a claim in ℝ: read down to ℝ, as an instance is",
    },
    Site {
        file: "lean/Parley/Proofs/Hammack/ChooseTwoEven/ChooseTwoFormula.lean",
        step: "1.2",
        holds: "exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3",
        list: false,
        why: "an item in ℤ for a claim in ℚ, one statement once the narrower is cast up, whose casts norm_cast all moves: exact_mod_cast",
    },
    Site {
        file: "lean/Parley/Tests/Elaborator/ListedSetsInAnyOrder/APairFromLines.lean",
        step: "1",
        holds: "Set.ext_iff",
        list: false,
        why: "the checker paired a listed set's members out of their places (its meeting's permuted), {w, u} for {u, w}: the equation of sets taken member by member",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/Harmonic/HarmonicUnbounded.lean",
        step: "2.2",
        holds: "simp only [Int.cast_one, div_one] at h",
        list: false,
        why: "the identity the checker's meeting names, 1 / 1, all that stands apart, its 1 written cast up by the function applied: the cast taken off, then div_one",
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
        holds: "congrArg (fun t : ℚ => (t ^ 2 - 1) / 8) e_w",
        list: false,
        why: "a define's equation of integers put into a side of the claim in ℚ, at places all of its arithmetic: stated in ℚ first, then congrArg of the motive in ℚ",
    },
    Site {
        file: "lean/Parley/Proofs/Hammack/FibonacciSum/FibonacciSum.lean",
        step: "5",
        holds: "exact",
        list: false,
        why: "an instance Lean takes as the claim, its terms one with the claim's in one type (forms::one_term_once_set): exact",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/RealsUncountable/DecimalNumber.lean",
        step: "5.4",
        holds: "linarith [",
        list: false,
        why: "an instance order with the claim's casts, over the same atoms: linarith",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/Binomial/BinomialStep.lean",
        step: "30",
        holds: "linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_add",
        list: false,
        why: "a calculation row citing an item's equation the route leaves to the closer: casts push_cast moves within each side, the same atoms, facing known: linear_combination",
    },
    Site {
        file: "lean/Parley/Proofs/Hammack/SumOfCubes/SumOfCubes.lean",
        step: "1.1",
        holds: "by parley_instance (",
        list: false,
        why: "a calculation row citing an item's equation in the row's type, (fun j => (j : ℚ) ^ 3) k beside k ^ 3: the item read in the row's spelling, parley_instance",
    },
    Site {
        file: "lean/Parley/Proofs/Setmm/EmptySum/EmptySum.lean",
        step: "2",
        holds: "simpa only [zero_add] using",
        list: false,
        why: "an item's equation whose atoms differ inside, ∑ over Icc (0 + 1) 0 beside Icc 1 0, which ring1 does not work in: met by the identity the checker's meeting names, simpa only [zero_add]",
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
        holds: "exact",
        list: false,
        why: "an instance of a for all over a set, ∀ x ∈ U, which the writer reads as a binder: Lean takes it as the claim, exact",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/LiouvilleNumber/LaterAtMost.lean",
        step: "2.4",
        holds: "parley_zpow_toNat (n := (LeanBridges.Counting.factorial (n + 1) : ℤ) + (i - n)) (h := add_nonneg (Nat.cast_nonneg _) (s2_1))",
        list: false,
        why: "an instance whose power the line writes as the integer power 2^((n + 1)! + (i − n)) and the instance to the exponent's toNat: converted, the exponent's fact named from the record, line 2.1 the step cites (forms_converted)",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/Wilson/Wilson.lean",
        step: "5.14.6",
        holds: "exact (s5_9 a hK8)",
        list: false,
        why: "a restate of a \"for all\" line read at the block's letter (CheckedTheorem::restated), its guard the let line that puts the letter in its range (ReadAt::opened_by)",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/RealsUncountable/DecimalNumber.lean",
        step: "16.21",
        holds: "have r607_2 : 0 ≤ d n := by exact (hH2 n hK6).1",
        list: false,
        why: "a requires line reasoned from lines alone, a part of a \"for all\" line read at the block's letter (CheckedTheorem::restated)",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/Wilson/Wilson.lean",
        step: "5.15.1",
        holds: "exact (s5_5 (f a) (s5_13 a hK9))",
        list: false,
        why: "an instantiation's value put in its domain by a \"for all\" line the step names, read at the block's letter (Instantiated::guards)",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/RealsUncountable/DecimalNumber.lean",
        step: "15.2",
        holds: "exact (s13b (U k : ℝ) (s10 k hK5))",
        list: false,
        why: "an instantiation's condition, \"if u is an upper bound of S\", met by a line the step names read at the block's letter (Instantiated::conditions)",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/RealsUncountable/DecimalNumber.lean",
        step: "6.4.1",
        holds: ".mpr ⟨by parley_set_side, r405_1⟩",
        list: false,
        why: "a definition read backwards, its right side's parts each from where the checker found it (Cited::unfolded): k − j an integer, which no line states, and 0 ≤ k − j, the step's requires line",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/RealsUncountable/DecimalNumber.lean",
        step: "3.16",
        holds: "(by exact_mod_cast s3_9.1) (by exact_mod_cast gt_iff_lt.mp r256_3)",
        list: false,
        why: "hypotheses supplied by lines in ℤ where the item asks them in ℚ: taken across by exact_mod_cast, which the cast table says moves the order, the line saying > turned to the < Lean asks first",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/Wilson/Wilson.lean",
        step: "5.15.7",
        holds: "s5_12 (by simpa only [Finset.mem_Icc, Set.mem_Icc] using hK9)",
        list: false,
        why: "an item's hypotheses over a range the citation gives, taken from the lines the checker found them in before parley_whole_side: the subset as line 5.12 states it, and the membership the let line writes as a Finset.Icc met as the Set.Icc Lean asks (Meets::Ranges)",
    },
    Site {
        file: "lean/Parley/Proofs/Setmm/BoundedBySquare/BoundedBySquare.lean",
        step: "6.5",
        holds: "exact le_trans s6_4 s6_3",
        list: false,
        why: "a transitivity chain whose links stand in lines, all in one type: composed by the lemma for each pair of relations (CheckedTheorem::links)",
    },
    Site {
        file: "lean/Parley/Proofs/Wiedijk/RealsUncountable/DecimalNumber.lean",
        step: "16.17",
        holds: "exact_mod_cast lt_of_le_of_lt s16_12 s16_16",
        list: false,
        why: "a transitivity chain in ℝ whose claim is in ℤ: composed, then taken to the claim's type by exact_mod_cast",
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
