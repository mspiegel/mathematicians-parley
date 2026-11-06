module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.OneNotInALongListedSet

theorem one_not_in_a_long_listed_set :
    ¬ (1 : ℤ) ∈ ({(2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ)} : Set ℤ) := by
  -- 1. inspection
  have s1 : ¬ (1 : ℤ) ∈ ({(2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ)} : Set ℤ) := by parley_set_side
  all_goals exact s1

end Parley.Tests.Notations.Sets.OneNotInALongListedSet
