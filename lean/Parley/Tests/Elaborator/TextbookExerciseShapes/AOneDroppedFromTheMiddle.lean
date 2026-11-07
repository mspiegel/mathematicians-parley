module

public import NormTactics
public import PowerTactics
public import SubstTactics
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
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AOneDroppedFromTheMiddle

theorem a_one_dropped_from_the_middle (b : ℤ → ℝ) (k : ℤ) (j : ℤ) (hH3 : 0 ≤ j) :
    b k * 1 ^ j.toNat * 1 ^ k = b k * 1 ^ k := by
  -- 1. mun:one-power m := j
  have s1 : (1 ^ j.toNat : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_one_power (m := j)) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_one_power (m := j)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_one_power (m := j))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := j)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := j)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := j)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := j)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := j)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := j)); parley_side)
  -- 2. substitute 1^j = 1 (line 1)
  have s2 : b k * 1 ^ j.toNat * 1 ^ k = b k * 1 ^ k := by
    have s1_w : (1 ^ j.toNat : ℝ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s1; push_cast at h; linear_combination (norm := parley_norm) h
    first | parley_subst s1_w | parley_subst s1
  all_goals exact s2

end Parley.Tests.Elaborator.TextbookExerciseShapes.AOneDroppedFromTheMiddle
