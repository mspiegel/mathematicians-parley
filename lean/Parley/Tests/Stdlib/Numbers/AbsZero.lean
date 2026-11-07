module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsZero

theorem abs_zero :
    (abs 0 : ℤ) = 0 := by
  -- 1. mun:numbers-abs-zero
  have s1 : (abs 0 : ℤ) = 0 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Numbers.mun_abs_zero | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Numbers.mun_abs_zero | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_zero).symm | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; parley_int_power h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_zero; parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.AbsZero
