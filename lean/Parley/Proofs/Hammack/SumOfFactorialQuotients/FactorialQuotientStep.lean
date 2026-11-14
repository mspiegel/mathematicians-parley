module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from proofs/hammack/sum-of-factorial-quotients.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfFactorialQuotients.FactorialQuotientStep

theorem factorial_quotient_step (c : ℤ) (hH1 : 0 < c) (F : ℝ) (hH3 : F ≠ 0) :
    1 - 1 / F + (c : ℝ) / (F * ((c : ℝ) + 1)) = 1 - 1 / (F * ((c : ℝ) + 1)) := by
  -- 1. algebra
  have r71_1 : F ≠ 0 := by exact hH3
  have s1 : (c : ℝ) / (F * ((c : ℝ) + 1)) = 1 / F * ((c : ℝ) / ((c : ℝ) + 1)) := by have hz1 : F ≠ 0 := r71_1; have hz2 : (c : ℝ) + 1 ≠ 0 := (by positivity); field
  -- 2. algebra
  have s2 : (c : ℚ) / ((c : ℚ) + 1) = 1 - 1 / ((c : ℚ) + 1) := by have hz1 : (c : ℚ) + 1 ≠ 0 := (by positivity); field
  -- 3. algebra
  have r78_1 : F ≠ 0 := by exact hH3
  have s3 : 1 / (F * ((c : ℝ) + 1)) = 1 / F * (1 / ((c : ℝ) + 1)) := by have hz1 : F ≠ 0 := r78_1; have hz2 : (c : ℝ) + 1 ≠ 0 := (by positivity); field
  -- 4. calculation
  have r82_1 : F ≠ 0 := by exact hH3
  calc 1 - 1 / F + (c : ℝ) / (F * ((c : ℝ) + 1)) = 1 - 1 / F + 1 / F * ((c : ℝ) / ((c : ℝ) + 1)) := congrArg (fun t : ℝ => 1 - 1 / F + t) s1
    _ = 1 - 1 / F + 1 / F * (1 - 1 / ((c : ℝ) + 1)) := by
        have e_w : (c : ℝ) / ((c : ℝ) + 1) = 1 - 1 / ((c : ℝ) + 1) := by have h := congrArg (fun x : ℚ => (x : ℝ)) s2; push_cast at h; linear_combination h
        exact congrArg (fun t : ℝ => 1 - 1 / F + 1 / F * t) e_w
    _ = 1 - 1 / F * (1 / ((c : ℝ) + 1)) := by have hz1 : F ≠ 0 := r82_1; have hz2 : (c : ℝ) + 1 ≠ 0 := (by positivity); field
    _ = 1 - 1 / (F * ((c : ℝ) + 1)) := congrArg (fun t : ℝ => 1 - t) s3.symm

end Parley.Proofs.Hammack.SumOfFactorialQuotients.FactorialQuotientStep
