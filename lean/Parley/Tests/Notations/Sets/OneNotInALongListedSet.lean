module

public import LeanBridges

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.OneNotInALongListedSet

theorem one_not_in_a_long_listed_set :
    ¬ ((1 : ℤ) = 2 ∨ (1 : ℤ) = 3 ∨ (1 : ℤ) = 4 ∨ (1 : ℤ) = 5 ∨ (1 : ℤ) = 6 ∨ (1 : ℤ) = 7 ∨ (1 : ℤ) = 8 ∨ (1 : ℤ) = 9) := by
  -- 1. inspection
  have s1 : ¬ ((1 : ℤ) = 2 ∨ (1 : ℤ) = 3 ∨ (1 : ℤ) = 4 ∨ (1 : ℤ) = 5 ∨ (1 : ℤ) = 6 ∨ (1 : ℤ) = 7 ∨ (1 : ℤ) = 8 ∨ (1 : ℤ) = 9) := by parley_side
  all_goals parley_side

end Parley.Tests.Notations.Sets.OneNotInALongListedSet
