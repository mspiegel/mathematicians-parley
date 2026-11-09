module

public import AlgebraTactics
public import ArithTactics
public import Functions
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.ProductOfOneMinusHalves.PowerOfTwoAtLeastFour
public import Parley.Proofs.Hammack.ProductStepBound.ProductStepBound

/-! Written from proofs/hammack/product-of-one-minus-halves.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ProductOfOneMinusHalves.ProductOfOneMinusHalves

set_option maxHeartbeats 400000 in
theorem product_of_one_minus_halves (n : ℤ) (hH1 : 0 < n) :
    (∏ k ∈ Finset.Icc (1 : ℤ) n, (1 - 1 / 2 ^ k.toNat : ℚ)) ≥ 1 / 4 + 1 / 2 ^ (n + 1).toNat := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. induction on m starting at 1
  have s2 : ∀ m : ℤ, 0 < m → (∏ k ∈ Finset.Icc (1 : ℤ) m, (1 - 1 / 2 ^ k.toNat : ℚ)) ≥ 1 / 4 + 1 / 2 ^ (m + 1).toNat := by
    intro m h_m
    replace h_m : 1 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 2.1. calculation
      calc (∏ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 - 1 / 2 ^ k.toNat : ℚ)) = 1 - 1 / 2 ^ 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ))); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ))); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ))); parley_side)
        _ ≥ 1 / 4 + 1 / 2 ^ (1 + 1) := by norm_num
    | succ m hK2 hIH =>
      -- 2.2. thm:power-of-two-at-least-four
      have s2_2 : (2 ^ (m + 1).toNat : ℤ) ≥ 4 := by exact (Parley.Proofs.Hammack.ProductOfOneMinusHalves.PowerOfTwoAtLeastFour.power_of_two_at_least_four (m := m) (by parley_side))
      -- 2.3. mun:power-nat a := 2, m := m + 1
      have s2_3 : (0 : ℤ) < 2 ^ (m + 1).toNat := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := (2 : ℤ)) (by parley_side) (m := m + 1) (by parley_side))
      -- 2.4. inequalities, from 2.3
      have s2_4 : (2 ^ (m + 1).toNat : ℤ) > 0 := by parley_order
      -- 2.5. mun:reciprocal-positive x := 2^(m + 1), from 2.4
      have s2_5 : (1 / 2 ^ (m + 1).toNat : ℚ) > 0 := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ (m + 1).toNat : ℚ)) (by parley_side))
      -- 2.6. mun:reciprocal-order x := 4, y := 2^(m + 1), from 2.2, 2.4
      have r84_1 : (4 : ℤ) > 0 := by parley_arith
      have s2_6 : (1 / 2 ^ (m + 1).toNat : ℚ) ≤ 1 / 4 := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (4 : ℚ)) (by parley_side) (y := (2 ^ (m + 1).toNat : ℚ)) (by parley_side))).mp (by parley_side)
      -- 2.7. mun:product-real a := 1, b := m, from 1
      -- 2.8. mun:exponent-step a := 2, m := m + 1
      have s2_8 : (2 ^ (m + 1 + 1).toNat : ℤ) = 2 ^ (m + 1).toNat * 2 := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m + 1) (by parley_side))
      -- 2.9. algebra
      have s2_9 : (1 / 4 + 1 / 2 ^ (m + 1).toNat / 2 : ℚ) = 1 / 4 + 1 / (2 ^ (m + 1).toNat * 2) := by parley_ring
      -- 2.10. calculation
      have r97_1 : m ≥ 1 := by parley_order
      calc (∏ k ∈ Finset.Icc (1 : ℤ) (m + 1), (1 - 1 / 2 ^ k.toNat : ℚ)) = (∏ k ∈ Finset.Icc (1 : ℤ) m, (1 - 1 / 2 ^ k.toNat : ℚ)) * (1 - 1 / 2 ^ (m + 1).toNat) := (Parley.Items.Stdlib.Sums.mun_product_extended (t := (fun k : ℤ => (1 - 1 / 2 ^ k.toNat : ℚ))) (a := (1 : ℤ)) (n := m) r97_1)
        _ ≥ 1 / 4 + 1 / 2 ^ (m + 1).toNat / 2 := by first | (have h := (Parley.Proofs.Hammack.ProductStepBound.ProductStepBound.product_step_bound (t := (1 / 2 ^ (m + 1).toNat : ℝ)) (p := ∏ k ∈ Finset.Icc (1 : ℤ) m, (1 - 1 / 2 ^ k.toNat : ℝ)) (by parley_side) (by parley_side) (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Proofs.Hammack.ProductStepBound.ProductStepBound.product_step_bound (t := (1 / 2 ^ (m + 1).toNat : ℝ)) (p := ∏ k ∈ Finset.Icc (1 : ℤ) m, (1 - 1 / 2 ^ k.toNat : ℝ)) (by parley_side) (by parley_side) (by parley_side))] | (have h := (Parley.Proofs.Hammack.ProductStepBound.ProductStepBound.product_step_bound (t := (1 / 2 ^ (m + 1).toNat : ℝ)) (p := ∏ k ∈ Finset.Icc (1 : ℤ) m, (1 - 1 / 2 ^ k.toNat : ℝ)) (by parley_side) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.ProductStepBound.ProductStepBound.product_step_bound (t := (1 / 2 ^ (m + 1).toNat : ℝ)) (p := ∏ k ∈ Finset.Icc (1 : ℤ) m, (1 - 1 / 2 ^ k.toNat : ℝ)) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Hammack.ProductStepBound.ProductStepBound.product_step_bound (t := (1 / 2 ^ (m + 1).toNat : ℝ)) (p := ∏ k ∈ Finset.Icc (1 : ℤ) m, (1 - 1 / 2 ^ k.toNat : ℝ)) (by parley_side) (by parley_side) (by parley_side)); parley_side)
        _ = 1 / 4 + 1 / (2 ^ (m + 1).toNat * 2) := by parley_side
        _ = 1 / 4 + 1 / 2 ^ (m + 1 + 1).toNat := by
            have s2_8_w : (2 ^ (m + 1 + 1).toNat : ℚ) = 2 ^ (m + 1).toNat * 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_8; push_cast at h; linear_combination (norm := parley_norm) h
            first | parley_subst s2_8_w | parley_subst s2_8
  -- 3. instantiate m := n in line 2
  exact (s2 n (by parley_side))

end Parley.Proofs.Hammack.ProductOfOneMinusHalves.ProductOfOneMinusHalves
