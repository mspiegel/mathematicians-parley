module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.AFourthPowerOfASquare

theorem a_fourth_power_of_a_square (x : ℝ) :
    x ^ 4 = (x ^ 2) ^ 2 := by
  -- 1. algebra
  have s1 : x ^ 4 = (x ^ 2) ^ 2 := by parley_ring
  all_goals exact s1

end Parley.Tests.Notations.Numbers.AFourthPowerOfASquare
