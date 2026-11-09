module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Counting

/-! Written from tests/stdlib/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Counting.SizeOfARange

theorem size_of_a_range :
    ((Set.Icc (1 : ℤ) (12 : ℤ) : Set ℤ).ncard : ℤ) = 12 := by
  -- 1. mun:range-size n := 12
  exact (Parley.Items.Stdlib.Counting.mun_range_size (n := (12 : ℤ)) (by parley_set_side))

end Parley.Tests.Stdlib.Counting.SizeOfARange
