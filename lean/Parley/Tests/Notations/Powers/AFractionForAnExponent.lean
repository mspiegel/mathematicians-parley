module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.AFractionForAnExponent

theorem a_fraction_for_an_exponent (x : ℝ) (hH2 : x ≥ 0) :
    True := by
  -- 1. mun:real-power-real y := 1/3, from H2
  exact trivial

end Parley.Tests.Notations.Powers.AFractionForAnExponent
