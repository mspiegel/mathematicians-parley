module

public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.ARealPowerOfAPositiveReal

theorem a_real_power_of_a_positive_real (x : ℝ) (hH2 : x > 0) (y : ℝ) :
    x ^ y > 0 := by
  -- 1. mun:real-power-positive, from H2
  exact (Parley.Items.Stdlib.Numbers.mun_real_power_positive (x := x) hH2 (y := y))

end Parley.Tests.Notations.Powers.ARealPowerOfAPositiveReal
