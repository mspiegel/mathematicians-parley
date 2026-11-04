module

public import SetTactics
public import Tactics

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.APairCounted

theorem a_pair_counted :
    (({(1 : ℤ), (2 : ℤ)} : Set ℤ).ncard : ℤ) = 2 := by
  -- 1. inspection
  have s1 : (({(1 : ℤ), (2 : ℤ)} : Set ℤ).ncard : ℤ) = 2 := by parley_set_side
  all_goals exact s1

end Parley.Tests.Notations.Sets.APairCounted
