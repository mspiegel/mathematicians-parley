module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusThreeInteger

theorem minus_three_integer :
    True := by
  -- 1. arithmetic
  exact trivial

end Parley.Tests.Notations.Negatives.MinusThreeInteger
