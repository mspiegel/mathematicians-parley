module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/a-map-written-short.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMapWrittenShort.AMembershipBeforeNoArrow

theorem a_membership_before_no_arrow (x : ℝ) (hH2 : ∃ m : ℤ, 0 < m ∧ (m : ℝ) = x) :
    (∃ m : ℤ, 0 < m ∧ (m : ℝ) = x) := by
  -- 1. restate H2
  parley_side

end Parley.Tests.Elaborator.AMapWrittenShort.AMembershipBeforeNoArrow
