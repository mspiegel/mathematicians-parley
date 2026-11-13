module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-map-written-short.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMapWrittenShort.AMembershipBeforeNoArrow

theorem a_membership_before_no_arrow (x : ℝ) (hH2 : ∃ m : ℤ, 0 < m ∧ (m : ℝ) = x) :
    (∃ m : ℤ, 0 < m ∧ (m : ℝ) = x) := by
  -- 1. restate H2
  exact hH2

end Parley.Tests.Elaborator.AMapWrittenShort.AMembershipBeforeNoArrow
