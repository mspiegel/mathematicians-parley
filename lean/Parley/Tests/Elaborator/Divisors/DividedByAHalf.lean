module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/divisors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Divisors.DividedByAHalf

theorem divided_by_a_half (x : ℝ) (hH2 : x ≠ 0) :
    3 / (x / 2) = 6 / x := by
  -- 1. algebra
  have r42_1 : x ≠ 0 := by exact hH2
  have hz1 : x ≠ 0 := r42_1; field

end Parley.Tests.Elaborator.Divisors.DividedByAHalf
