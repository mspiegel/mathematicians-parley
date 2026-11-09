module

public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-sum-over-a-compound-of-a-defined-function.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASumOverACompoundOfADefinedFunction.ASumOfSquaresOfARecursion

theorem a_sum_of_squares_of_a_recursion (F : ℤ → ℤ) (hD1 : F 0 = (1 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 1)) (hH1 : True) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (F j ^ 2 : ℤ)) = F 1 ^ 2 := by
  -- 1. mun:sum-single a := 1, from H1
  exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => F j ^ 2)) (a := (1 : ℤ)))

end Parley.Tests.Elaborator.ASumOverACompoundOfADefinedFunction.ASumOfSquaresOfARecursion
