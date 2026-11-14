module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/a-cited-conclusion-without-its-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor

theorem doubled_successor (n : ℤ) (hH1 : 0 ≤ n) :
    2 * (n + 1) = 2 * n + 2 := by
  -- 1. calculation
  calc 2 * (n + 1) = 2 * (n + 1) := rfl
    _ = 2 * n + 2 := by ring1
    _ = 2 * n + 2 := rfl

end Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor
