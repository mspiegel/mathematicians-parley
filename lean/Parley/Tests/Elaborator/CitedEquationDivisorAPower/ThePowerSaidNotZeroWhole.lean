module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/cited-equation-divisor-a-power.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CitedEquationDivisorAPower.ThePowerSaidNotZeroWhole

theorem the_power_said_not_zero_whole (t : ℝ) (F : ℝ) (hH3 : t ≠ 0) (hH4 : F = 1 / t ^ 2) :
    F * t ^ 2 = 1 := by
  -- 1. mun:square-positive x := t, from H3
  have s1 : t ^ 2 > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_positive (x := t) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := t) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_positive (x := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := t) (by parley_side)); parley_side)
  -- 2. algebra, from H4
  have r42_1 : t ^ 2 ≠ 0 := by parley_side
  have s2 : F * t ^ 2 = 1 := by linear_combination (norm := parley_field) (t ^ 2) * hH4
  all_goals parley_side

end Parley.Tests.Elaborator.CitedEquationDivisorAPower.ThePowerSaidNotZeroWhole
