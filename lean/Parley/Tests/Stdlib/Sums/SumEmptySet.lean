module

public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.SumEmptySet

theorem sum_empty_set :
    (∑ᶠ k ∈ (∅ : Set ℤ), (k ^ 2 : ℤ)) = 0 := by
  -- 1. mun:sums-sum-empty-set
  exact (Parley.Items.Stdlib.Sums.mun_sum_empty_set (t := (fun k : ℤ => k ^ 2)))

end Parley.Tests.Stdlib.Sums.SumEmptySet
