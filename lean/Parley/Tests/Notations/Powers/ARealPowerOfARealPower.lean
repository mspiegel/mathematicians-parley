module

public import ComplexTactics
public import PowerTactics
public import Tactics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.ARealPowerOfARealPower

theorem a_real_power_of_a_real_power (x : ℝ) (hH2 : x > 0) (a : ℝ) (b : ℝ) :
    x ^ (a * b) = (x ^ a) ^ b := by
  -- 1. mun:real-power-of-power, from H2
  have s1 : x ^ (a * b) = (x ^ a) ^ b := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_real_power_of_power (x := x) (by parley_side) (a := a) (b := (b : ℂ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_of_power (x := x) (by parley_side) (a := a) (b := (b : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_of_power (x := x) (by parley_side) (a := a) (b := (b : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_real_power_of_power (x := x) (by parley_side) (a := a) (b := (b : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_real_power_of_power (x := x) (by parley_side) (a := a) (b := (b : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_of_power (x := x) (by parley_side) (a := a) (b := (b : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_of_power (x := x) (by parley_side) (a := a) (b := (b : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_of_power (x := x) (by parley_side) (a := a) (b := (b : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_of_power (x := x) (by parley_side) (a := a) (b := (b : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_of_power (x := x) (by parley_side) (a := a) (b := (b : ℂ))); parley_side)
  all_goals exact s1

end Parley.Tests.Notations.Powers.ARealPowerOfARealPower
