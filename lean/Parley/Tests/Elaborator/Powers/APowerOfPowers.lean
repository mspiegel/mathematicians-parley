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

/-! Written from tests/elaborator/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Powers.APowerOfPowers

theorem a_power_of_powers (x : ℝ) :
    ((x ^ 3) ^ 3) ^ 3 = x ^ 27 := by
  -- 1. algebra
  have s1 : ((x ^ 3) ^ 3) ^ 3 = x ^ 27 := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.Powers.APowerOfPowers
