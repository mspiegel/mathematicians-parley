module

public import SetTactics
public import Tactics
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.APairCounted

theorem a_pair_counted :
    ({(1 : ℤ), (2 : ℤ)} : Set ℤ).encard = ((2 : ℕ) : ℕ∞) := by
  -- 1. inspection
  have s1 : ({(1 : ℤ), (2 : ℤ)} : Set ℤ).encard = ((2 : ℕ) : ℕ∞) := by parley_set_side
  all_goals exact s1

end Parley.Tests.Notations.Sets.APairCounted
