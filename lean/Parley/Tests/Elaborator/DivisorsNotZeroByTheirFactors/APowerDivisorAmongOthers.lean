module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/divisors-not-zero-by-their-factors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.APowerDivisorAmongOthers

theorem a_power_divisor_among_others (k : ℤ) (hH2 : k > 0) :
    1 / (k : ℚ) - 1 / ((k : ℚ) + 1) - 1 / ((k : ℚ) + 1) ^ 2 = 1 / ((k : ℚ) * ((k : ℚ) + 1) ^ 2) := by
  -- 1. inequalities, from H2
  have s1 : k + 1 > 0 := by parley_order
  -- 2. algebra
  have r16_1 : k ≠ 0 := by parley_side
  have r16_2 : k + 1 ≠ 0 := by parley_side
  have s2 : 1 / (k : ℚ) - 1 / ((k : ℚ) + 1) - 1 / ((k : ℚ) + 1) ^ 2 = 1 / ((k : ℚ) * ((k : ℚ) + 1) ^ 2) := by parley_ring
  all_goals exact s2

end Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.APowerDivisorAmongOthers
