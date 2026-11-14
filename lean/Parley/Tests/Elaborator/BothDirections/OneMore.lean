module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

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
    linear_combination hD1
  · skip
    intro hD2
    -- 1.2. algebra, from D2
    linear_combination hD2

end Parley.Tests.Elaborator.BothDirections.OneMore
