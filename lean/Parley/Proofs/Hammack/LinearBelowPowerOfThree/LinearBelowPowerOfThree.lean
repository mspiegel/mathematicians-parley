module

public import ArithTactics
public import Functions
public import OrderTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/linear-below-power-of-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LinearBelowPowerOfThree.LinearBelowPowerOfThree

theorem linear_below_power_of_three (n : ℤ) (hH1 : 0 < n) :
    2 * n + 1 ≤ 3 ^ n.toNat := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → 2 * k + 1 ≤ 3 ^ k.toNat := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (2 * 1 + 1 : ℤ) ≤ 3 ^ 1 := by parley_arith
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. mun:exponent-step a := 3
      have s1_2 : (3 ^ (k + 1).toNat : ℤ) = 3 ^ k.toNat * 3 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k) (by parley_side)); parley_side)
      -- 1.3. inequalities
      have s1_3 : 6 * k + 3 ≤ 3 ^ k.toNat * 3 := by parley_order
      -- 1.4. inequalities, from K
      have s1_4 : 0 < k := by parley_order
      -- 1.5. inequalities
      have s1_5 : 2 * (k + 1) + 1 ≤ 6 * k + 3 := by parley_order
      -- 1.6. transitivity, from 1.5, 1.3, 1.2
      have s1_6 : 2 * (k + 1) + 1 ≤ 3 ^ (k + 1).toNat := by parley_order
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : 2 * n + 1 ≤ 3 ^ n.toNat := by first | (have h := (s1 n (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(s1 n (by parley_side))] | (have h := (s1 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.LinearBelowPowerOfThree.LinearBelowPowerOfThree
