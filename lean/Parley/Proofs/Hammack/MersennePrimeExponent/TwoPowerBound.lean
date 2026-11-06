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

/-! Written from proofs/hammack/mersenne-prime-exponent.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound

theorem two_power_bound (d : ℤ) (hH1 : 0 < d) :
    2 ^ d.toNat ≥ d + 1 := by
  -- 1. induction on m starting at 1
  have s1 : ∀ m : ℤ, 0 < m → 2 ^ m.toNat ≥ m + 1 := by
    intro m h_m
    replace h_m : 1 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (2 ^ 1 : ℤ) ≥ 1 + 1 := by parley_arith
      all_goals parley_side
    | succ m hK hIH =>
      -- 1.2. mun:exponent-step a := 2
      have s1_2 : (2 ^ (m + 1).toNat : ℤ) = 2 ^ m.toNat * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m) (by parley_side)); parley_side)
      -- 1.3. inequalities
      have s1_3 : 2 ^ m.toNat * 2 ≥ (m + 1) * 2 := by parley_order
      -- 1.4. inequalities, from K
      have s1_4 : (m + 1) * 2 ≥ m + 1 + 1 := by parley_order
      -- 1.5. transitivity, from 1.2, 1.3, 1.4
      have s1_5 : 2 ^ (m + 1).toNat ≥ m + 1 + 1 := by parley_order
      all_goals parley_side
  -- 2. instantiate m := d in line 1
  have s2 : 2 ^ d.toNat ≥ d + 1 := by first | (have h := (s1 d (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(s1 d (by parley_side))] | (have h := (s1 d (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 d (by parley_side)) | (have h := (s1 d (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound
