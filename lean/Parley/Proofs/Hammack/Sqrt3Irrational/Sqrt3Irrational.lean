module

public import AlgebraTactics
public import ArithTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
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
public import Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms

/-! Written from proofs/hammack/sqrt3-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.Sqrt3Irrational.Sqrt3Irrational

set_option maxHeartbeats 400000 in
theorem sqrt3_irrational :
    Irrational (Real.sqrt (3 : ℝ)) := by
  -- 1. def:sqrt x := 3
  have r139_1 : (3 : ℤ) ≥ 0 := by parley_arith
  have s1 : Real.sqrt (3 : ℝ) ^ 2 = 3 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (3 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (3 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (3 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (3 : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (3 : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (3 : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (3 : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (3 : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (3 : ℝ)) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (3 : ℝ)) (by parley_side)); parley_side)
  -- 2. contradiction
  have s2 : ¬ (∃ m : ℚ, (m : ℝ) = Real.sqrt (3 : ℝ)) := by
    by_contra hc_hS
    have hS : ∃ m : ℚ, (m : ℝ) = Real.sqrt (3 : ℝ) := by parley_suppose hc_hS
    -- 2.1. obtain p, q: thm:lowest-terms x := √3, from S
    obtain ⟨p, q, ⟨⟨s2_1a, s2_1b⟩, s2_1c⟩⟩ := (Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms.lowest_terms (x := (Classical.choose hS)))
    have s2_1b : Real.sqrt (3 : ℝ) = (p : ℝ) / (q : ℝ) := by rw [← Classical.choose_spec hS]; exact_mod_cast s2_1b
    -- 2.2. substitute √3 = p/q (line 2.1) into line 1
    have s2_2 : ((p : ℚ) / (q : ℚ)) ^ 2 = 3 := by parley_subst_at s2_1b s1
    -- 2.3. algebra, from 2.2
    have r154_1 : q ≠ 0 := by parley_side
    have s2_3 : p ^ 2 = 3 * q ^ 2 := by qify at *; linear_combination (norm := parley_field) ((q : ℚ) ^ 2) * s2_2
    -- 2.4. def:divides d := 3, n := p², from 2.3
    have s2_4 : (3 : ℤ) ∣ p ^ 2 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p ^ 2))).mpr ⟨q ^ 2, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p ^ 2))).mpr ⟨q ^ 2, by parley_side⟩; parley_side)
    -- 2.5. thm:three-divides-square n := p, from 2.4
    have s2_5 : (3 : ℤ) ∣ p := by first | exact (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := p) s2_4) | exact ((Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := p) s2_4)).symm | simpa using (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := p) s2_4) | exact_mod_cast (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := p) s2_4) | (have h := (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := p) s2_4); parley_side)
    -- 2.6. obtain r: def:divides d := 3, n := p, from 2.5
    obtain ⟨r, s2_6⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p))).mp (by parley_side)
    -- 2.7. substitute p = 3r (line 2.6) into line 2.3
    have s2_7 : (3 * r) ^ 2 = 3 * q ^ 2 := by parley_subst_at s2_6 s2_3
    -- 2.8. algebra, from 2.7
    have s2_8 : q ^ 2 = 3 * r ^ 2 := by qify at *; linear_combination (norm := parley_norm) (-(1 / 3 : ℚ)) * s2_7
    -- 2.9. def:divides d := 3, n := q², from 2.8
    have s2_9 : (3 : ℤ) ∣ q ^ 2 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := q ^ 2))).mpr ⟨r ^ 2, by parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := q ^ 2))).mpr ⟨r ^ 2, by parley_side⟩; parley_side)
    -- 2.10. thm:three-divides-square n := q, from 2.9
    have s2_10 : (3 : ℤ) ∣ q := by first | exact (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := q) s2_9) | exact ((Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := q) s2_9)).symm | simpa using (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := q) s2_9) | exact_mod_cast (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := q) s2_9) | (have h := (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := q) s2_9); parley_side)
    -- 2.11. exhibit, from 2.5, 2.10
    have r179_1 : (3 : ℤ) > 1 := by parley_arith
    have s2_11 : ∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q := ⟨(3 : ℤ), ⟨⟨by parley_side, by parley_side⟩, by parley_side⟩⟩
    all_goals parley_side
  -- 3. def:irrational x := √3, from 2
  have s3 : Irrational (Real.sqrt (3 : ℝ)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (3 : ℝ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (3 : ℝ)))).mpr (by parley_side); parley_side)
  all_goals exact s3

end Parley.Proofs.Hammack.Sqrt3Irrational.Sqrt3Irrational
