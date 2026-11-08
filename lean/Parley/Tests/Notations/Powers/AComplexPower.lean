module

public import Tactics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.AComplexPower

theorem a_complex_power (z : ℂ) (w : ℂ) :
    True := by
  -- 1. mun:real-power-complex x := z, y := w
  exact trivial

end Parley.Tests.Notations.Powers.AComplexPower
