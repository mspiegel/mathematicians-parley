module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import Tactics
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
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
  have s1 : Real.sqrt (3 : ℝ) ^ 2 = 3 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (3 : ℝ)) (by parley_side))
  -- 2. contradiction
  have s2 : ¬ (∃ m : ℚ, (m : ℝ) = Real.sqrt (3 : ℝ)) := by
    intro hS
    -- 2.1. obtain p, q: thm:lowest-terms x := √3, from S
    obtain ⟨p, q, ⟨⟨s2_1a, s2_1b⟩, s2_1c⟩⟩ := (Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms.lowest_terms (x := (Classical.choose hS)))
    have s2_1b : Real.sqrt (3 : ℝ) = (p : ℝ) / (q : ℝ) := by rw [← Classical.choose_spec hS]; exact_mod_cast s2_1b
    -- 2.2. substitute √3 = p/q (line 2.1) into line 1
    have s2_2 : ((p : ℚ) / (q : ℚ)) ^ 2 = 3 := by (have h := Eq.subst (motive := (fun t : ℝ => t ^ 2 = 3)) s2_1b s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 2.3. algebra, from 2.2
    have r154_1 : q ≠ 0 := by parley_side
    have s2_3 : p ^ 2 = 3 * q ^ 2 := by qify at *; linear_combination (norm := parley_field) ((q : ℚ) ^ 2) * s2_2
    -- 2.4. def:divides d := 3, n := p², from 2.3
    have s2_4 : (3 : ℤ) ∣ p ^ 2 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p ^ 2))).mpr ⟨q ^ 2, s2_3⟩
    -- 2.5. thm:three-divides-square n := p, from 2.4
    have s2_5 : (3 : ℤ) ∣ p := by exact (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := p) (by parley_side))
    -- 2.6. obtain r: def:divides d := 3, n := p, from 2.5
    obtain ⟨r, s2_6⟩ := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := p))).mp s2_5
    -- 2.7. substitute p = 3r (line 2.6) into line 2.3
    have s2_7 : (3 * r) ^ 2 = 3 * q ^ 2 := by (have h := Eq.subst (motive := (fun t : ℤ => t ^ 2 = 3 * q ^ 2)) s2_6 s2_3; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 2.8. algebra, from 2.7
    have s2_8 : q ^ 2 = 3 * r ^ 2 := by qify at *; linear_combination (norm := parley_norm) (-(1 / 3 : ℚ)) * s2_7
    -- 2.9. def:divides d := 3, n := q², from 2.8
    have s2_9 : (3 : ℤ) ∣ q ^ 2 := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (3 : ℤ)) (n := q ^ 2))).mpr ⟨r ^ 2, s2_8⟩
    -- 2.10. thm:three-divides-square n := q, from 2.9
    have s2_10 : (3 : ℤ) ∣ q := by exact (Parley.Proofs.Hammack.Sqrt3Irrational.ThreeDividesSquare.three_divides_square (n := q) (by parley_side))
    -- 2.11. exhibit, from 2.5, 2.10
    have r179_1 : (3 : ℤ) > 1 := by parley_arith
    have s2_11 : ∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q := ⟨(3 : ℤ), ⟨⟨r179_1, s2_5⟩, s2_10⟩⟩
    exact s2_1c s2_11
  -- 3. def:irrational x := √3, from 2
  exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (3 : ℝ)))).mpr (by parley_side)

end Parley.Proofs.Hammack.Sqrt3Irrational.Sqrt3Irrational
