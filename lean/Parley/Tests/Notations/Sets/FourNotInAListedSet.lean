module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Set

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.FourNotInAListedSet

theorem four_not_in_a_listed_set :
    ¬ (4 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ), (3 : ℤ)} : Set ℤ) := by
  set S : Set ℤ := ({(1 : ℤ), (2 : ℤ), (3 : ℤ)} : Set ℤ) with hD1
  have hD1_finite : S.Finite := by rw [hD1]; exact Set.toFinite _
  -- 1. inspection, from D1
  simp [hD1]

end Parley.Tests.Notations.Sets.FourNotInAListedSet
