module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import NormTactics
public import OrderTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/product-of-one-minus-halves.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ProductOfOneMinusHalves.PowerOfTwoAtLeastFour

theorem power_of_two_at_least_four (m : ℤ) (hH1 : 0 < m) :
    (2 ^ (m + 1).toNat : ℤ) ≥ 4 := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → (2 ^ (k + 1).toNat : ℤ) ≥ 4 := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (2 ^ (1 + 1) : ℤ) ≥ 4 := by parley_arith
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. mun:power-nat a := 2, m := k + 1
      have s1_2 : (0 : ℤ) < 2 ^ (k + 1).toNat := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by parley_side) (m := k + 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by parley_side) (m := k + 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by parley_side) (m := k + 1) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by parley_side) (m := k + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by parley_side) (m := k + 1) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by parley_side) (m := k + 1) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by parley_side) (m := k + 1) (by parley_side)); parley_side)
      -- 1.3. inequalities, from 1.2
      have s1_3 : (2 ^ (k + 1).toNat : ℤ) ≥ 0 := by parley_order
      -- 1.4. inequalities, from IH, 1.3
      have s1_4 : (2 ^ (k + 1).toNat + 2 ^ (k + 1).toNat : ℤ) ≥ 4 := by parley_order
      -- 1.5. calculation
      have s1_5 : (2 ^ (k + 1 + 1).toNat : ℤ) ≥ 4 := by
        calc (2 ^ (k + 1 + 1).toNat : ℤ) = 2 ^ (k + 1).toNat * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); parley_side)
          _ = 2 ^ (k + 1).toNat + 2 ^ (k + 1).toNat := by parley_ring
          _ ≥ 4 := by first | parley_side | parley_line_toNat s1_4
      all_goals parley_side
  -- 2. instantiate k := m in line 1
  have s2 : (2 ^ (m + 1).toNat : ℤ) ≥ 4 := by first | (have h := (s1 m (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(s1 m (by parley_side))] | (have h := (s1 m (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 m (by parley_side)) | (have h := (s1 m (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.ProductOfOneMinusHalves.PowerOfTwoAtLeastFour
