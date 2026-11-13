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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/an-item-at-a-member.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnItemAtAMember.AnItemAtAMemberAsAStep

theorem an_item_at_a_member_as_a_step (B : ℤ → ℝ) :
    True := by
  -- 1. mun:sum-real a := 1, b := m
  exact trivial

end Parley.Tests.Elaborator.AnItemAtAMember.AnItemAtAMemberAsAStep
