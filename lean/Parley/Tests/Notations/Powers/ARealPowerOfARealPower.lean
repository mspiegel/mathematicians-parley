module

public import ComplexTactics
public import Tactics
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.ARealPowerOfARealPower

theorem a_real_power_of_a_real_power (x : ℝ) (hH2 : x > 0) (a : ℝ) (b : ℝ) :
    x ^ (a * b) = (x ^ a) ^ b := by
  -- 1. mun:real-power-of-power, from H2
  (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_of_power (x := x) hH2 (a := a) (b := (b : ℂ))); parley_of_complex h)

end Parley.Tests.Notations.Powers.ARealPowerOfARealPower
