module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.OneToZeroIsEmpty

theorem one_to_zero_is_empty :
    (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) = ∅ := by
  -- 1. mun:range-empty
  have s1 : (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) = ∅ := by exact Parley.Items.Stdlib.Sums.mun_range_empty
  all_goals exact s1

end Parley.Tests.Notations.Counting.OneToZeroIsEmpty
