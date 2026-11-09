module

public import AlgebraTactics
public import NormTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from proofs/hammack/sum-of-factorial-quotients.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfFactorialQuotients.FactorialQuotientStep

theorem factorial_quotient_step (c : ℤ) (hH1 : 0 < c) (F : ℝ) (hH3 : F ≠ 0) :
    1 - 1 / F + (c : ℝ) / (F * ((c : ℝ) + 1)) = 1 - 1 / (F * ((c : ℝ) + 1)) := by
  -- 1. algebra
  have r71_1 : F ≠ 0 := by parley_side
  have s1 : (c : ℝ) / (F * ((c : ℝ) + 1)) = 1 / F * ((c : ℝ) / ((c : ℝ) + 1)) := by parley_ring
  -- 2. algebra
  have s2 : (c : ℚ) / ((c : ℚ) + 1) = 1 - 1 / ((c : ℚ) + 1) := by parley_ring
  -- 3. algebra
  have r78_1 : F ≠ 0 := by parley_side
  have s3 : 1 / (F * ((c : ℝ) + 1)) = 1 / F * (1 / ((c : ℝ) + 1)) := by parley_ring
  -- 4. calculation
  have r82_1 : F ≠ 0 := by parley_side
  calc 1 - 1 / F + (c : ℝ) / (F * ((c : ℝ) + 1)) = 1 - 1 / F + 1 / F * ((c : ℝ) / ((c : ℝ) + 1)) := by (have h := congrArg (fun t : ℝ => 1 - 1 / F + t) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = 1 - 1 / F + 1 / F * (1 - 1 / ((c : ℝ) + 1)) := by
        have s2_w : (c : ℝ) / ((c : ℝ) + 1) = 1 - 1 / ((c : ℝ) + 1) := by have h := congrArg (fun x : ℚ => (x : ℝ)) s2; push_cast at h; linear_combination (norm := parley_norm) h
        first | parley_subst s2_w | parley_subst s2
    _ = 1 - 1 / F * (1 / ((c : ℝ) + 1)) := by parley_ring
    _ = 1 - 1 / (F * ((c : ℝ) + 1)) := by (have h := congrArg (fun t : ℝ => 1 - t) (s3).symm; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Hammack.SumOfFactorialQuotients.FactorialQuotientStep
