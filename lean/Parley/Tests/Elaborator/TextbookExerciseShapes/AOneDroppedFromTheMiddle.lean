module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AOneDroppedFromTheMiddle

theorem a_one_dropped_from_the_middle (b : ℤ → ℝ) (k : ℤ) (j : ℤ) (hH3 : 0 ≤ j) :
    b k * 1 ^ j.toNat * 1 ^ k = b k * 1 ^ k := by
  -- 1. mun:one-power m := j
  have s1 : (1 ^ j.toNat : ℤ) = 1 := by (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := j)); simp only [parley_zpow_toNat (n := j) (h := hH3)] at h ⊢; exact_mod_cast h)
  -- 2. substitute 1^j = 1 (line 1)
  have e_w : (1 ^ j.toNat : ℝ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s1; push_cast at h; linear_combination (norm := parley_norm) h
  (have h := congrArg (fun t : ℝ => b k * t * 1 ^ k) e_w; push_cast [mul_one] at h ⊢; all_goals exact_mod_cast h)

end Parley.Tests.Elaborator.TextbookExerciseShapes.AOneDroppedFromTheMiddle
