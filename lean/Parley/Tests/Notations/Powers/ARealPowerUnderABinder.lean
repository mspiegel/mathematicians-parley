module

public import ArithTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.ARealPowerUnderABinder

theorem a_real_power_under_a_binder :
    (∀ y : ℝ, (2 : ℝ) ^ y > 0) := by
  -- 1. proof
  have s1 : ∀ y : ℝ, (2 : ℝ) ^ y > 0 := by
    intro y
    -- 1.1. mun:real-power-positive x := 2
    have r65_1 : (2 : ℤ) > 0 := by parley_arith
    have s1_1 : (2 : ℝ) ^ y > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_real_power_positive (x := (2 : ℝ)) (by parley_side) (y := y))] | (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_positive (x := (2 : ℝ)) (by parley_side) (y := y)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_real_power_positive (x := (2 : ℝ)) (by parley_side) (y := y)) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_positive (x := (2 : ℝ)) (by parley_side) (y := y)); parley_side)
    all_goals exact s1_1
  all_goals exact s1

end Parley.Tests.Notations.Powers.ARealPowerUnderABinder
