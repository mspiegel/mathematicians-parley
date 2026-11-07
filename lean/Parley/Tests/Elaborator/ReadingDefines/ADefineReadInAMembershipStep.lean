module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAMembershipStep

theorem a_define_read_in_a_membership_step (a : ℝ) (hH2 : a + 1 ≠ 0) :
    True := by
  set e : ℝ := a + 1 with hD1
  -- 1. membership, from D1, H2
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAMembershipStep
