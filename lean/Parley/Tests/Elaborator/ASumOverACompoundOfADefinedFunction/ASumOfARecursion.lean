module

public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-sum-over-a-compound-of-a-defined-function.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASumOverACompoundOfADefinedFunction.ASumOfARecursion

theorem a_sum_of_a_recursion (F : ℤ → ℤ) (hD1 : F 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 1) (hH1 : True) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (F j : ℤ)) = F 1 := by
  -- 1. mun:sum-single a := 1
  exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := F) (a := (1 : ℤ)))

end Parley.Tests.Elaborator.ASumOverACompoundOfADefinedFunction.ASumOfARecursion
