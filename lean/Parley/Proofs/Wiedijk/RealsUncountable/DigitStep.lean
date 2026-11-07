module

public import AlgebraTactics
public import ArithTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides

/-! Written from proofs/wiedijk/reals-uncountable.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.RealsUncountable.DigitStep

theorem digit_step (t : ℤ) :
    (t + 1) % (10 : ℤ) ≠ t := by
  -- 1. thm:digit-step-divides
  have s1 : (10 : ℤ) ∣ t + 1 - (t + 1) % (10 : ℤ) := by exact (Parley.Proofs.Wiedijk.RealsUncountable.DigitStepDivides.digit_step_divides (t := t))
  -- 2. contradiction
  have s2 : (t + 1) % (10 : ℤ) ≠ t := by
    by_contra hc_hS1
    have hS1 : (t + 1) % (10 : ℤ) = t := by parley_suppose hc_hS1
    -- 2.1. substitute s(t) = t (S1) into line 1
    have s2_1 : (10 : ℤ) ∣ t + 1 - t := by parley_subst_at hS1 s1
    -- 2.2. substitute
    have s2_2 : (10 : ℤ) ∣ (1 : ℤ) := by
      have c1 : t + 1 - t = 1 := by parley_ring
      have row1 : (10 : ℤ) ∣ (1 : ℤ) := by parley_subst_at c1 s2_1
      exact row1
    exact absurd s2_2 (by norm_num)
    all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Wiedijk.RealsUncountable.DigitStep
