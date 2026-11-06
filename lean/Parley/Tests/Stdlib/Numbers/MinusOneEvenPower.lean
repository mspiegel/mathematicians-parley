module

public import PowerTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.MinusOneEvenPower

theorem minus_one_even_power (n : ℤ) :
    ((-1) ^ (2 * n) : ℚ) = 1 := by
  -- 1. mun:numbers-minus-one-even-power
  have s1 : ((-1) ^ (2 * n) : ℚ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_minus_one_even_power (n := n)) | (have h := (Parley.Items.Stdlib.Numbers.mun_minus_one_even_power (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_minus_one_even_power (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_minus_one_even_power (n := n)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_minus_one_even_power (n := n))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_minus_one_even_power (n := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_minus_one_even_power (n := n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_minus_one_even_power (n := n)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_minus_one_even_power (n := n)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.MinusOneEvenPower
