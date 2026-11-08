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
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Tests.Notations.Sums.OneToThreeSummed

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.OneToThreeNotFive

theorem one_to_three_not_five :
    (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) ≠ 5 := by
  -- 1. thm:one-to-three-summed
  have s1 : (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) = 6 := by exact Parley.Tests.Notations.Sums.OneToThreeSummed.one_to_three_summed
  -- 2. contradiction
  intro hS
  -- 2.1. calculation
  have s2_1 : (6 : ℤ) = 5 := by
    calc (6 : ℤ) = (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) := by parley_side
      _ = 5 := by parley_side
  exact absurd s2_1 (by norm_num)

end Parley.Tests.Notations.Sums.OneToThreeNotFive
