module

public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.AHalfPower

theorem a_half_power (x : ℝ) :
    (x : ℂ) ^ (1 / 2 : ℂ) = (x : ℂ) ^ (1 / 2 : ℂ) := by
  -- 1. mun:half-power
  have s1 : (x : ℂ) ^ (1 / 2 : ℂ) = (x : ℂ) ^ (1 / 2 : ℂ) := by exact (Parley.Items.Stdlib.Numbers.mun_half_power (x := (x : ℂ)))
  all_goals exact s1

end Parley.Tests.Notations.Powers.AHalfPower
