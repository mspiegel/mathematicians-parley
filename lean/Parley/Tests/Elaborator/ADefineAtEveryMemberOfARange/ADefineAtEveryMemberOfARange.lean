module

public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-define-at-every-member-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineAtEveryMemberOfARange.ADefineAtEveryMemberOfARange

theorem a_define_at_every_member_of_a_range (m : ℤ) (hH1 : 0 < m) (q : ℤ → ℤ) (hD1 : ∀ j : ℤ, 0 < j → q j = j + 1) :
    (∀ j : ℤ, j ∈ Finset.Icc 1 m → q j = j + 1) := by
  -- 1. D1
  (try simp only [hD1]); first | done | parley_side

end Parley.Tests.Elaborator.ADefineAtEveryMemberOfARange.ADefineAtEveryMemberOfARange
