module

public import Tactics

/-! Written from tests/elaborator/a-define-at-every-member-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineAtEveryMemberOfARange.ADefineAtEveryMemberOfARange

theorem a_define_at_every_member_of_a_range (m : ℤ) (hH1 : 0 < m) (q : ℤ → ℤ) (hD1 : ∀ j : ℤ, 0 < j → q j = j + 1) :
    (∀ j : ℤ, j ∈ Finset.Icc 1 m → q j = j + 1) := by
  -- 1. D1
  have s1 : ∀ j : ℤ, j ∈ Finset.Icc 1 m → q j = j + 1 := by (try simp only [hD1]); first | done | parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ADefineAtEveryMemberOfARange.ADefineAtEveryMemberOfARange
