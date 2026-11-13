module

public import SetTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-square-in-a-divisor-said-nonzero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASquareInADivisorSaidNonzero.ARequiresLineAtAnIntervalMember

theorem a_requires_line_at_an_interval_member :
    (∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True) := by
  -- 1. membership
  have r25_1 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), x ^ 2 ≥ 0 := by intro x h_x; (exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)))
  have r25_2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), 1 + x ^ 2 > 0 := by intro x h_x; (linarith only [r25_1 x h_x])
  intro x h_x; exact by trivial

end Parley.Tests.Elaborator.ASquareInADivisorSaidNonzero.ARequiresLineAtAnIntervalMember
