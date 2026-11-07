module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnPower

theorem ln_power (x : ℝ) (n : ℤ) (hH3 : x > 0) :
    Real.log (x ^ n) = (n : ℝ) * Real.log x := by
  -- 1. mun:logarithms-ln-power, from H3
  have s1 : Real.log (x ^ n) = (n : ℝ) * Real.log x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := x) (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := x) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := x) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := x) (n := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_power (x := x) (n := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := x) (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := x) (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := x) (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_power (x := x) (n := n) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Logarithms.LnPower
