module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerOfPowerInteger

theorem power_of_power_integer (z : ℂ) (hH2 : z ≠ 0) (j : ℤ) (k : ℤ) :
    z ^ (j * k) = (z ^ j) ^ k := by
  -- 1. mun:numbers-power-of-power-integer a := z, m := j, n := k, from H2
  have s1 : z ^ (j * k) = (z ^ j) ^ k := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_power_of_power_integer (a := z) (by parley_side) (m := j) (n := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power_integer (a := z) (by parley_side) (m := j) (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power_integer (a := z) (by parley_side) (m := j) (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_of_power_integer (a := z) (by parley_side) (m := j) (n := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_power_of_power_integer (a := z) (by parley_side) (m := j) (n := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power_integer (a := z) (by parley_side) (m := j) (n := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power_integer (a := z) (by parley_side) (m := j) (n := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power_integer (a := z) (by parley_side) (m := j) (n := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power_integer (a := z) (by parley_side) (m := j) (n := k)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerOfPowerInteger
