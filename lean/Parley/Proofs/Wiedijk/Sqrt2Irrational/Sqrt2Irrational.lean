module

public import AlgebraTactics
public import ArithTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Even
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms

/-! Written from proofs/wiedijk/sqrt2-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational

set_option maxHeartbeats 400000 in
theorem sqrt2_irrational :
    Irrational (Real.sqrt (2 : ℝ)) := by
  -- 1. def:sqrt x := 2
  have r104_1 : (2 : ℤ) ≥ 0 := by parley_arith
  have s1 : Real.sqrt (2 : ℝ) ^ 2 = 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); parley_side)
  -- 2. contradiction
  have s2 : ¬ (∃ m : ℚ, (m : ℝ) = Real.sqrt (2 : ℝ)) := by
    by_contra hc_hS
    have hS : ∃ m : ℚ, (m : ℝ) = Real.sqrt (2 : ℝ) := by parley_suppose hc_hS
    -- 2.1. obtain p, q: thm:lowest-terms x := √2, from S
    obtain ⟨p, q, ⟨⟨s2_1a, s2_1b⟩, s2_1c⟩⟩ := (Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms.lowest_terms (x := (Classical.choose hS)))
    have s2_1b : Real.sqrt (2 : ℝ) = (p : ℝ) / (q : ℝ) := by rw [← Classical.choose_spec hS]; exact_mod_cast s2_1b
    -- 2.2. substitute √2 = p/q (line 2.1) into line 1
    have s2_2 : ((p : ℚ) / (q : ℚ)) ^ 2 = 2 := by parley_subst_at s2_1b s1
    -- 2.3. algebra, from 2.2
    have r119_1 : q ≠ 0 := by parley_side
    have s2_3 : p ^ 2 = 2 * q ^ 2 := by qify at *; linear_combination (norm := parley_field) ((q : ℚ) ^ 2) * s2_2
    -- 2.4. def:even n := p², from 2.3
    have s2_4 : Even (p ^ 2) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := p ^ 2))).mpr ⟨q ^ 2, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := p ^ 2))).mpr ⟨q ^ 2, by parley_side⟩; parley_side)
    -- 2.5. thm:even-square n := p, from 2.4
    have s2_5 : Even p := by first | exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := p) s2_4) | exact ((Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := p) s2_4)).symm | simpa using (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := p) s2_4) | exact_mod_cast (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := p) s2_4) | (have h := (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := p) s2_4); parley_side)
    -- 2.6. obtain r: def:even n := p, from 2.5
    obtain ⟨r, s2_6⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := p))).mp (by parley_side)
    -- 2.7. calculation
    have s2_7 : 2 * q ^ 2 = 4 * r ^ 2 := by
      calc 2 * q ^ 2 = p ^ 2 := by parley_side
        _ = (2 * r) ^ 2 := by parley_subst s2_6
        _ = 4 * r ^ 2 := by parley_ring
    -- 2.8. algebra, from 2.7
    have s2_8 : q ^ 2 = 2 * r ^ 2 := by qify at *; linear_combination (norm := parley_norm) ((1 / 2 : ℚ)) * s2_7
    -- 2.9. def:even n := q², from 2.8
    have s2_9 : Even (q ^ 2) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_even (n := q ^ 2))).mpr ⟨r ^ 2, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_even (n := q ^ 2))).mpr ⟨r ^ 2, by parley_side⟩; parley_side)
    -- 2.10. thm:even-square n := q, from 2.9
    have s2_10 : Even q := by first | exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := q) s2_9) | exact ((Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := q) s2_9)).symm | simpa using (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := q) s2_9) | exact_mod_cast (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := q) s2_9) | (have h := (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := q) s2_9); parley_side)
    -- 2.11. obtain s: def:even n := q, from 2.10
    obtain ⟨s, s2_11⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := q))).mp (by parley_side)
    -- 2.12. def:divides d := 2, n := p, from 2.6
    have s2_12 : (2 : ℤ) ∣ p := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := p))).mpr ⟨r, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := p))).mpr ⟨r, by parley_side⟩; parley_side)
    -- 2.13. def:divides d := 2, n := q, from 2.11
    have s2_13 : (2 : ℤ) ∣ q := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := q))).mpr ⟨s, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := q))).mpr ⟨s, by parley_side⟩; parley_side)
    -- 2.14. exhibit, from 2.12, 2.13
    have r156_1 : (2 : ℤ) > 1 := by parley_arith
    have s2_14 : ∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q := ⟨(2 : ℤ), ⟨⟨by parley_side, by parley_side⟩, by parley_side⟩⟩
    all_goals parley_side
  -- 3. def:irrational x := √2, from 2
  have s3 : Irrational (Real.sqrt (2 : ℝ)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (2 : ℝ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (2 : ℝ)))).mpr (by parley_side); parley_side)
  all_goals exact s3

end Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational
