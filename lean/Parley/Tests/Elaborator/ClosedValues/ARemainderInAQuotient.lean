module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.ARemainderInAQuotient

theorem a_remainder_in_a_quotient :
    -6 ≠ 536 * (((2 : ℤ) % (216 : ℤ) : ℤ) : ℚ) / 1 := by
  -- 1. arithmetic
  norm_num

end Parley.Tests.Elaborator.ClosedValues.ARemainderInAQuotient
