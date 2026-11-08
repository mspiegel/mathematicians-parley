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

namespace Parley.Tests.Notations.Numbers.ACubeMultipliedOut

theorem a_cube_multiplied_out (x : ℝ) :
    (x + 1) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 := by
  -- 1. algebra
  parley_ring

end Parley.Tests.Notations.Numbers.ACubeMultipliedOut
