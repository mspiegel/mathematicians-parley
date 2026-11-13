module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-sum-of-defined-values-said-pointwise.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASumOfDefinedValuesSaidPointwise.ASumOfDefinedValuesSaidPointwise

theorem a_sum_of_defined_values_said_pointwise (m : ℤ) (hH1 : 0 < m) (F : ℤ → ℤ) (hD1 : F 0 = (1 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 1)) :
    True := by
  -- 1. membership, from H2
  exact trivial

end Parley.Tests.Elaborator.ASumOfDefinedValuesSaidPointwise.ASumOfDefinedValuesSaidPointwise
