module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.RemainderOfASmallNumber

theorem remainder_of_a_small_number :
    (4 : ℤ) % (7 : ℤ) = 4 := by
  -- 1. arithmetic
  norm_num

end Parley.Tests.Elaborator.LargeArithmetic.RemainderOfASmallNumber
