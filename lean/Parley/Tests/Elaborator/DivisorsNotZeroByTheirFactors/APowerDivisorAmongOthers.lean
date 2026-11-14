module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/divisors-not-zero-by-their-factors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.APowerDivisorAmongOthers

theorem a_power_divisor_among_others (k : ℤ) (hH2 : k > 0) :
    1 / (k : ℚ) - 1 / ((k : ℚ) + 1) - 1 / ((k : ℚ) + 1) ^ 2 = 1 / ((k : ℚ) * ((k : ℚ) + 1) ^ 2) := by
  -- 1. inequalities, from H2
  have s1 : k + 1 > 0 := by linarith only [hH2]
  -- 2. algebra
  have r16_1 : k ≠ 0 := ne_of_gt (by linarith only [hH2])
  have r16_2 : k + 1 ≠ 0 := ne_of_gt (by linarith only [s1])
  have hz1 : (k : ℚ) ≠ 0 := (by exact_mod_cast r16_1); have hz2 : (k : ℚ) + 1 ≠ 0 := (by exact_mod_cast r16_2); field

end Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.APowerDivisorAmongOthers
