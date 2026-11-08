module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-sum-of-defined-values-said-pointwise.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASumOfDefinedValuesSaidPointwise.ASumOfDefinedValuesSaidPointwise

theorem a_sum_of_defined_values_said_pointwise (m : ℤ) (hH1 : 0 < m) (F : ℤ → ℤ) (hD1 : F 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 1) (hH2 : True) :
    True := by
  -- 1. membership, from H2
  exact trivial

end Parley.Tests.Elaborator.ASumOfDefinedValuesSaidPointwise.ASumOfDefinedValuesSaidPointwise
