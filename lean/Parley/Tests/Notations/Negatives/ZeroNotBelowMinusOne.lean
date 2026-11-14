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
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.ZeroNotBelowMinusOne

theorem zero_not_below_minus_one :
    ¬ (0 : ℤ) < -1 := by
  -- 1. arithmetic
  norm_num

end Parley.Tests.Notations.Negatives.ZeroNotBelowMinusOne
