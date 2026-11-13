module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.OneNotInALongListedSet

theorem one_not_in_a_long_listed_set :
    ¬ (1 : ℤ) ∈ ({(2 : ℤ), (3 : ℤ), (4 : ℤ), (5 : ℤ), (6 : ℤ), (7 : ℤ), (8 : ℤ), (9 : ℤ)} : Set ℤ) := by
  -- 1. inspection
  simp

end Parley.Tests.Notations.Sets.OneNotInALongListedSet
