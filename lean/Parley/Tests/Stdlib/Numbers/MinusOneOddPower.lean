module

public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.MinusOneOddPower

theorem minus_one_odd_power (n : ℤ) (hH2 : Odd n) :
    ((-1) ^ n : ℚ) = -1 := by
  -- 1. mun:numbers-minus-one-odd-power, from H2
  have s1 : ((-1) ^ n : ℚ) = -1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_minus_one_odd_power (n := n) hH2) | (have h := (Parley.Items.Stdlib.Numbers.mun_minus_one_odd_power (n := n) hH2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_minus_one_odd_power (n := n) hH2); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_minus_one_odd_power (n := n) hH2) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_minus_one_odd_power (n := n) hH2)).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_minus_one_odd_power (n := n) hH2); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_minus_one_odd_power (n := n) hH2); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_minus_one_odd_power (n := n) hH2); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_minus_one_odd_power (n := n) hH2); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.MinusOneOddPower
