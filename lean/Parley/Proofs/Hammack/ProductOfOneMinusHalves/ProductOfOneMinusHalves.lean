module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.ProductOfOneMinusHalves.PowerOfTwoAtLeastFour
public import Parley.Proofs.Hammack.ProductStepBound.ProductStepBound

/-! Written from proofs/hammack/product-of-one-minus-halves.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ProductOfOneMinusHalves.ProductOfOneMinusHalves

theorem product_of_one_minus_halves (n : ℕ) (hH1 : 0 < n) :
    (∏ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 - 1 / 2 ^ k : ℚ)) ≥ 1 / 4 + 1 / 2 ^ (n + 1) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. induction on m starting at 1
  have s2 : ∀ m : ℕ, 0 < m → (∏ k ∈ Finset.Icc (1 : ℤ) (m : ℤ), (1 - 1 / 2 ^ k : ℚ)) ≥ 1 / 4 + 1 / 2 ^ (m + 1) := by
    intro m h_m
    replace h_m : 1 ≤ m := h_m
    induction m, h_m using Nat.le_induction with
    | base =>
      -- 2.1. calculation
      have s2_1 : (∏ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 - 1 / 2 ^ k : ℚ)) ≥ 1 / 4 + 1 / 2 ^ (1 + 1) := by
        calc (∏ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 - 1 / 2 ^ k : ℚ)) = 1 - 1 / 2 ^ 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_single (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ))); parley_side)
          _ ≥ 1 / 4 + 1 / 2 ^ (1 + 1) := by norm_num
      all_goals parley_side
    | succ m hK2 hIH =>
      -- 2.2. thm:power-of-two-at-least-four
      have s2_2 : (2 ^ (m + 1) : ℤ) ≥ 4 := by first | linarith [(Parley.Proofs.Hammack.ProductOfOneMinusHalves.PowerOfTwoAtLeastFour.power_of_two_at_least_four (m := m) (by parley_side))] | (have h := (Parley.Proofs.Hammack.ProductOfOneMinusHalves.PowerOfTwoAtLeastFour.power_of_two_at_least_four (m := m) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.ProductOfOneMinusHalves.PowerOfTwoAtLeastFour.power_of_two_at_least_four (m := m) (by parley_side)) | (have h := (Parley.Proofs.Hammack.ProductOfOneMinusHalves.PowerOfTwoAtLeastFour.power_of_two_at_least_four (m := m) (by parley_side)); parley_side)
      -- 2.3. mun:power-nat a := 2, m := m + 1
      have s2_3 : (0 : ℤ) < 2 ^ (m + 1) := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := m + 1)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := m + 1))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := m + 1)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := m + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := m + 1)); parley_side)
      -- 2.4. inequalities, from 2.3
      have s2_4 : (2 ^ (m + 1) : ℤ) > 0 := by parley_order
      -- 2.5. mun:reciprocal-positive x := 2^(m + 1), from 2.4
      have s2_5 : (1 / 2 ^ (m + 1) : ℚ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ (m + 1) : ℚ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ (m + 1) : ℚ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ (m + 1) : ℚ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ (m + 1) : ℚ)) (by parley_side)); parley_side)
      -- 2.6. mun:reciprocal-order x := 4, y := 2^(m + 1), from 2.2, 2.4
      have r84_1 : (4 : ℤ) > 0 := by parley_arith
      have s2_6 : (1 / 2 ^ (m + 1) : ℚ) ≤ 1 / 4 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (4 : ℚ)) (by parley_side) (y := (2 ^ (m + 1) : ℚ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (4 : ℚ)) (by parley_side) (y := (2 ^ (m + 1) : ℚ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (4 : ℚ)) (by parley_side) (y := (2 ^ (m + 1) : ℚ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (4 : ℚ)) (by parley_side) (y := (2 ^ (m + 1) : ℚ)) (by parley_side))).mp (by parley_side); parley_side)
      -- 2.7. mun:product-real a := 1, b := m, from 1
      -- 2.8. mun:exponent-step a := 2, m := m + 1
      have s2_8 : (2 ^ (m + 1 + 1) : ℤ) = 2 ^ (m + 1) * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m + 1))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m + 1)); parley_side)
      -- 2.9. algebra
      have s2_9 : (1 / 4 + 1 / 2 ^ (m + 1) / 2 : ℚ) = 1 / 4 + 1 / (2 ^ (m + 1) * 2) := by parley_ring
      -- 2.10. calculation
      have r97_1 : (m : ℤ) ≥ 1 := by parley_order
      have s2_10 : (∏ k ∈ Finset.Icc (1 : ℤ) ((m : ℤ) + 1), (1 - 1 / 2 ^ k : ℚ)) ≥ 1 / 4 + 1 / 2 ^ (m + 1 + 1) := by
        calc (∏ k ∈ Finset.Icc (1 : ℤ) ((m : ℤ) + 1), (1 - 1 / 2 ^ k : ℚ)) = (∏ k ∈ Finset.Icc (1 : ℤ) (m : ℤ), (1 - 1 / 2 ^ k : ℚ)) * (1 - 1 / 2 ^ (m + 1)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_extended (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_extended (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_extended (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := (fun k : ℤ => (1 - 1 / 2 ^ k : ℚ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); parley_side)
          _ ≥ 1 / 4 + 1 / 2 ^ (m + 1) / 2 := by first | linarith [(Parley.Proofs.Hammack.ProductStepBound.ProductStepBound.product_step_bound (t := (1 / 2 ^ (m + 1) : ℝ)) (p := ∏ k ∈ Finset.Icc (1 : ℤ) (m : ℤ), (1 - 1 / 2 ^ k : ℝ)) (by parley_side) (by parley_side) (by parley_side))] | (have h := (Parley.Proofs.Hammack.ProductStepBound.ProductStepBound.product_step_bound (t := (1 / 2 ^ (m + 1) : ℝ)) (p := ∏ k ∈ Finset.Icc (1 : ℤ) (m : ℤ), (1 - 1 / 2 ^ k : ℝ)) (by parley_side) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Hammack.ProductStepBound.ProductStepBound.product_step_bound (t := (1 / 2 ^ (m + 1) : ℝ)) (p := ∏ k ∈ Finset.Icc (1 : ℤ) (m : ℤ), (1 - 1 / 2 ^ k : ℝ)) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Proofs.Hammack.ProductStepBound.ProductStepBound.product_step_bound (t := (1 / 2 ^ (m + 1) : ℝ)) (p := ∏ k ∈ Finset.Icc (1 : ℤ) (m : ℤ), (1 - 1 / 2 ^ k : ℝ)) (by parley_side) (by parley_side) (by parley_side)); parley_side)
          _ = 1 / 4 + 1 / (2 ^ (m + 1) * 2) := by parley_side
          _ = 1 / 4 + 1 / 2 ^ (m + 1 + 1) := by
              have s2_8_w : (2 ^ (m + 1 + 1) : ℚ) = 2 ^ (m + 1) * 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_8; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s2_8_w | parley_subst s2_8
      all_goals parley_side
  -- 3. instantiate m := n in line 2
  have s3 : (∏ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 - 1 / 2 ^ k : ℚ)) ≥ 1 / 4 + 1 / 2 ^ (n + 1) := by first | linarith [(s2 n (by parley_side))] | (have h := (s2 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s2 n (by parley_side)) | (have h := (s2 n (by parley_side)); parley_side)
  all_goals exact s3

end Parley.Proofs.Hammack.ProductOfOneMinusHalves.ProductOfOneMinusHalves
