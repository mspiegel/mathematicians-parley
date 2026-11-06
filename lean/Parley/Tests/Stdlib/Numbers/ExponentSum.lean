module

public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.ExponentSum

theorem exponent_sum (a : ℝ) (m : ℤ) (hH2 : 0 ≤ m) (n : ℤ) (hH3 : 0 ≤ n) :
    a ^ (m + n).toNat = a ^ m.toNat * a ^ n.toNat := by
  -- 1. mun:numbers-exponent-sum
  have s1 : a ^ (m + n).toNat = a ^ m.toNat * a ^ n.toNat := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := a) (m := m) (by parley_side) (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := a) (m := m) (by parley_side) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := a) (m := m) (by parley_side) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := a) (m := m) (by parley_side) (n := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := a) (m := m) (by parley_side) (n := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := a) (m := m) (by parley_side) (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := a) (m := m) (by parley_side) (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := a) (m := m) (by parley_side) (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := a) (m := m) (by parley_side) (n := n) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := a) (m := m) (by parley_side) (n := n) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := a) (m := m) (by parley_side) (n := n) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.ExponentSum
