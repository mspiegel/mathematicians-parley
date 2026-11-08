module

public import NormTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/both-directions.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.BothDirections.OneMore

theorem one_more (n : ℤ) :
    (n + 1 = 3 ↔ n = 2) := by
  -- 1. both directions
  constructor
  · skip
    intro hD1
    -- 1.1. algebra, from D1
    linear_combination (norm := parley_norm) hD1
  · skip
    intro hD2
    -- 1.2. algebra, from D2
    linear_combination (norm := parley_norm) hD2

end Parley.Tests.Elaborator.BothDirections.OneMore
