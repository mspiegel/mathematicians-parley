module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic

/-! Written from tests/notations/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sets.FourNotInAWrittenSet

theorem four_not_in_a_written_set :
    ¬ (4 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ), (3 : ℤ)} : Set ℤ) := by
  -- 1. inspection
  have s1 : ¬ (4 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ), (3 : ℤ)} : Set ℤ) := by parley_set_side
  all_goals exact s1

end Parley.Tests.Notations.Sets.FourNotInAWrittenSet
