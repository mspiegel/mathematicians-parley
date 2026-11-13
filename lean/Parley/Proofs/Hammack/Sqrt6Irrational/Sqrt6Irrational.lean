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
public import Mathlib.Tactic.NormNum.Core
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

/-! Written from proofs/hammack/sqrt6-irrational.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.Sqrt6Irrational.Sqrt6Irrational

theorem sqrt6_irrational :
    Irrational (Real.sqrt (6 : ℝ)) := by
  -- 1. def:sqrt x := 6
  have r14_1 : (6 : ℤ) ≥ 0 := by parley_arith
  have s1 : Real.sqrt (6 : ℝ) ^ 2 = 6 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (6 : ℝ)) (by norm_num))
  -- 2. contradiction
  have s2 : ¬ (∃ m : ℚ, (m : ℝ) = Real.sqrt (6 : ℝ)) := by
    intro hS
    -- 2.1. obtain p, q: thm:lowest-terms x := √6, from S
    obtain ⟨p, q, ⟨⟨s2_1a, s2_1b⟩, s2_1c⟩⟩ := (Parley.Proofs.Wiedijk.Sqrt2Irrational.LowestTerms.lowest_terms (x := (Classical.choose hS)))
    have s2_1b : Real.sqrt (6 : ℝ) = (p : ℝ) / (q : ℝ) := by rw [← Classical.choose_spec hS]; exact_mod_cast s2_1b
    -- 2.2. substitute √6 = p/q (line 2.1) into line 1
    have s2_2 : ((p : ℚ) / (q : ℚ)) ^ 2 = 6 := by (have h := Eq.subst (motive := (fun t : ℝ => t ^ 2 = 6)) s2_1b s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 2.3. algebra, from 2.2
    have r29_1 : q ≠ 0 := ne_of_gt (by linarith only [s2_1a])
    have s2_3 : p ^ 2 = 6 * q ^ 2 := by qify at *; linear_combination (norm := parley_field) ((q : ℚ) ^ 2) * s2_2
    -- 2.4. algebra, from 2.3
    have s2_4 : p ^ 2 = 2 * (3 * q ^ 2) := by linear_combination (norm := parley_norm) s2_3
    -- 2.5. def:even n := p², from 2.4
    have s2_5 : Even (p ^ 2) := ((Parley.Items.Stdlib.Divisibility.def_even (n := p ^ 2))).mpr ⟨3 * q ^ 2, s2_4⟩
    -- 2.6. thm:even-square n := p, from 2.5
    have s2_6 : Even p := by exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := p) s2_5)
    -- 2.7. obtain r: def:even n := p, from 2.6
    obtain ⟨r, s2_7⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := p))).mp s2_6
    -- 2.8. substitute p = 2r (line 2.7) into line 2.3
    have s2_8 : (2 * r) ^ 2 = 6 * q ^ 2 := by (have h := Eq.subst (motive := (fun t : ℤ => t ^ 2 = 6 * q ^ 2)) s2_7 s2_3; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 2.9. algebra, from 2.8
    have s2_9 : 2 * r ^ 2 = 3 * q ^ 2 := by qify at *; linear_combination (norm := parley_norm) ((1 / 2 : ℚ)) * s2_8
    -- 2.10. algebra, from 2.9
    have s2_10 : q ^ 2 = 2 * (r ^ 2 - q ^ 2) := by linear_combination (norm := parley_norm) (-1) * s2_9
    -- 2.11. def:even n := q², from 2.10
    have s2_11 : Even (q ^ 2) := ((Parley.Items.Stdlib.Divisibility.def_even (n := q ^ 2))).mpr ⟨r ^ 2 - q ^ 2, s2_10⟩
    -- 2.12. thm:even-square n := q, from 2.11
    have s2_12 : Even q := by exact (Parley.Proofs.Wiedijk.Sqrt2Irrational.EvenSquare.even_square (n := q) s2_11)
    -- 2.13. obtain s: def:even n := q, from 2.12
    obtain ⟨s, s2_13⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := q))).mp s2_12
    -- 2.14. def:divides d := 2, n := p, from 2.7
    have s2_14 : (2 : ℤ) ∣ p := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := p))).mpr ⟨r, s2_7⟩
    -- 2.15. def:divides d := 2, n := q, from 2.13
    have s2_15 : (2 : ℤ) ∣ q := ((Parley.Items.Stdlib.Divisibility.def_divides (d := (2 : ℤ)) (n := q))).mpr ⟨s, s2_13⟩
    -- 2.16. exhibit, from 2.14, 2.15
    have r69_1 : (2 : ℤ) > 1 := by parley_arith
    have s2_16 : ∃ d : ℤ, (d > 1 ∧ d ∣ p) ∧ d ∣ q := ⟨(2 : ℤ), ⟨⟨by norm_num, s2_14⟩, s2_15⟩⟩
    exact s2_1c s2_16
  -- 3. def:irrational x := √6, from 2
  exact ((Parley.Items.Stdlib.Numbers.def_irrational (x := Real.sqrt (6 : ℝ)))).mpr ⟨by trivial, s2⟩

end Parley.Proofs.Hammack.Sqrt6Irrational.Sqrt6Irrational
