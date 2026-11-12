module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import Tactics
public import Batteries.Classes.RatCast
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
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
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare
public import Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms

/-! Written from proofs/wiedijk/sqrt2-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational

theorem sqrt2_irrational :
    Irrational (Real.sqrt (2 : ℝ)) := by
  -- 1. def:sqrt x := 2
  have r104_1 : (2 : ℤ) ≥ 0 := by parley_arith
  have s1 : Real.sqrt (2 : ℝ) ^ 2 = 2 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side))
  -- 2. contradiction
  have s2 : ¬ (∃ m : ℚ, (m : ℝ) = Real.sqrt (2 : ℝ)) := by
    intro hS
    -- 2.1. obtain p, q: thm:lowest-terms x := √2, from S
    obtain ⟨p, q, ⟨⟨s2_1a, s2_1b⟩, s2_1c⟩⟩ := (Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms.lowest_terms (x := (Classical.choose hS)))
    have s2_1b : Real.sqrt (2 : ℝ) = (p : ℝ) / (q : ℝ) := by rw [← Classical.choose_spec hS]; exact_mod_cast s2_1b
    -- 2.2. substitute √2 = p/q (line 2.1) into line 1
    have s2_2 : ((p : ℚ) / (q : ℚ)) ^ 2 = 2 := by (have h := Eq.subst (motive := (fun t : ℝ => t ^ 2 = 2)) s2_1b s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 2.3. algebra, from 2.2
    have r119_1 : q ≠ 0 := ne_of_gt (by linarith only [s2_1a])
    have s2_3 : p ^ 2 = 2 * q ^ 2 := by qify at *; linear_combination (norm := parley_field) ((q : ℚ) ^ 2) * s2_2
    -- 2.4. def:even n := p², from 2.3
    have s2_4 : Even (p ^ 2) := ((Parley.Items.Stdlib.Divisibility.def_even (n := p ^ 2))).mpr ⟨q ^ 2, s2_3⟩
    -- 2.5. thm:even-square n := p, from 2.4
    have s2_5 : Even p := by exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := p) s2_4)
    -- 2.6. obtain r: def:even n := p, from 2.5
    obtain ⟨r, s2_6⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := p))).mp s2_5
    -- 2.7. calculation
    have s2_7 : 2 * q ^ 2 = 4 * r ^ 2 := by
      calc 2 * q ^ 2 = p ^ 2 := by exact s2_3.symm
        _ = (2 * r) ^ 2 := by (have h := congrArg (fun t : ℤ => t ^ 2) s2_6; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 4 * r ^ 2 := by parley_ring
    -- 2.8. algebra, from 2.7
    have s2_8 : q ^ 2 = 2 * r ^ 2 := by qify at *; linear_combination (norm := parley_norm) ((1 / 2 : ℚ)) * s2_7
    -- 2.9. def:even n := q², from 2.8
    have s2_9 : Even (q ^ 2) := ((Parley.Items.Stdlib.Divisibility.def_even (n := q ^ 2))).mpr ⟨r ^ 2, s2_8⟩
    -- 2.10. thm:even-square n := q, from 2.9
    have s2_10 : Even q := by exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := q) s2_9)
    -- 2.11. obtain s: def:even n := q, from 2.10
    obtain ⟨s, s2_11⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := q))).mp s2_10
    -- 2.12. def:divides d := 2, n := p, from 2.6
    have s2_12 : (2 : ℤ) ∣ p := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := p))).mpr ⟨r, s2_6⟩
    -- 2.13. def:divides d := 2, n := q, from 2.11
    have s2_13 : (2 : ℤ) ∣ q := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := q))).mpr ⟨s, s2_11⟩
    -- 2.14. exhibit, from 2.12, 2.13
    have r156_1 : (2 : ℤ) > 1 := by parley_arith
    have s2_14 : ∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q := ⟨(2 : ℤ), ⟨⟨r156_1, s2_12⟩, s2_13⟩⟩
    exact s2_1c s2_14
  -- 3. def:irrational x := √2, from 2
  exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (2 : ℝ)))).mpr ⟨by parley_side, s2⟩

end Parley.Proofs.Wiedijk.Sqrt2Irrational.Sqrt2Irrational
