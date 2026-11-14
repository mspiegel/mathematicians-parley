module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Rat.Init
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

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.FractionsEqual

theorem fractions_equal :
    (2 / 4 : ℚ) ≤ 3 / 6 := by
  -- 1. arithmetic
  norm_num

end Parley.Tests.Elaborator.LargeArithmetic.FractionsEqual
