module

public import LeanBridges

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.APairCounted

theorem a_pair_counted :
    ({(1 : ℤ), (2 : ℤ)} : Set ℤ).encard = ((2 : ℕ) : ℕ∞) := by
  -- 1. inspection
  have s1 : ({(1 : ℤ), (2 : ℤ)} : Set ℤ).encard = ((2 : ℕ) : ℕ∞) := by parley_side
  all_goals parley_side

end Parley.Tests.Notations.Sets.APairCounted
