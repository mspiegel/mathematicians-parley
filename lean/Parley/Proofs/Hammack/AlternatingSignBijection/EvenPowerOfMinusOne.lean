module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne

theorem even_power_of_minus_one (k : ℤ) (hH1 : 0 ≤ k) :
    ((-1) ^ (2 * k).toNat : ℤ) = 1 := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℤ, 0 ≤ j → ((-1) ^ (2 * j).toNat : ℤ) = 1 := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : ((-1) ^ (2 * 0) : ℤ) = 1 := by parley_arith
      all_goals parley_side
    | succ j hK1 hIH =>
      -- 1.2. algebra
      have s1_2 : 2 * (j + 1) = 2 * j + 2 := by parley_ring
      -- 1.3. calculation
      have s1_3 : ((-1) ^ (2 * (j + 1)).toNat : ℤ) = 1 := by
        calc ((-1) ^ (2 * (j + 1)).toNat : ℤ) = (-1) ^ (2 * j + 2).toNat := by parley_subst s1_2
          _ = (-1) ^ (2 * j).toNat * (-1) ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (by parley_side) (n := (2 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (by parley_side) (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (by parley_side) (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (by parley_side) (n := (2 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (by parley_side) (n := (2 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (by parley_side) (n := (2 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (by parley_side) (n := (2 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (by parley_side) (n := (2 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (by parley_side) (n := (2 : ℤ)) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (by parley_side) (n := (2 : ℤ)) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := (-1 : ℤ)) (m := 2 * j) (by parley_side) (n := (2 : ℤ)) (by parley_side)); parley_side)
          _ = 1 * (-1) ^ 2 := by parley_subst hIH
          _ = 1 := by norm_num
      all_goals parley_side
  -- 2. instantiate j := k in line 1
  have s2 : ((-1) ^ (2 * k).toNat : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (s1 k (by parley_side)) | (have h := (s1 k (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 k (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 k (by parley_side)) | exact_mod_cast ((s1 k (by parley_side))).symm | (have h := (s1 k (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 k (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 k (by parley_side)); parley_int_power h) | (have h := (s1 k (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s1 k (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s1 k (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne
