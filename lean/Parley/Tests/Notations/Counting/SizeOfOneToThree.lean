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
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Counting

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.SizeOfOneToThree

theorem size_of_one_to_three :
    ((Set.Icc (1 : ℤ) (3 : ℤ) : Set ℤ).ncard : ℤ) = 3 := by
  -- 1. mun:range-size n := 3
  exact (Parley.Items.Stdlib.Counting.mun_range_size (n := (3 : ℤ)) (by norm_num))

end Parley.Tests.Notations.Counting.SizeOfOneToThree
