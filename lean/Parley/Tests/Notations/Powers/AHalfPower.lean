module

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

namespace Parley.Tests.Notations.Powers.AHalfPower

theorem a_half_power (x : ℝ) :
    (x : ℂ) ^ (1 / 2 : ℂ) = (x : ℂ) ^ (1 / 2 : ℂ) := by
  -- 1. mun:half-power
  have s1 : (x : ℂ) ^ (1 / 2 : ℂ) = (x : ℂ) ^ (1 / 2 : ℂ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_half_power (x := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_half_power (x := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_half_power (x := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_half_power (x := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_half_power (x := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_half_power (x := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_half_power (x := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_half_power (x := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_half_power (x := (x : ℂ))); parley_side)
  all_goals exact s1

end Parley.Tests.Notations.Powers.AHalfPower
