module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous
public import Parley.Proofs.Wiedijk.Leibniz.PowerIntegral

/-! Written from proofs/wiedijk/leibniz.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence

set_option maxHeartbeats 400000 in
theorem integral_recurrence (n : ℕ) :
    (∫ t in 0..1, (t ^ (2 * (n + 1)) / (1 + t ^ 2) : ℝ)) = 1 / (2 * (n : ℝ) + 1) - (∫ t in 0..1, (t ^ (2 * n) / (1 + t ^ 2) : ℝ)) := by
  set f : ℝ → ℝ := fun x => x ^ (2 * n) with hD1
  set g : ℝ → ℝ := fun x => x ^ (2 * n) / (1 + x ^ 2) with hD2
  set h : ℝ → ℝ := fun x => x ^ (2 * (n + 1)) / (1 + x ^ 2) with hD3
  -- 1. proof
  have s1 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), h x = f x - g x := by
    intro x hK1
    -- 1.1. algebra
    have s1_1 : 2 * ((n : ℤ) + 1) = 2 * (n : ℤ) + 2 := by parley_ring
    -- 1.2. calculation
    have s1_2 : x ^ (2 * (n + 1)) = x ^ (2 * n) * x ^ 2 := by
      calc x ^ (2 * (n + 1)) = x ^ (2 * n + 2) := by
            have s1_1_w : 2 * ((n : ℝ) + 1) = 2 * (n : ℝ) + 2 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s1_1; push_cast at h; linear_combination (norm := parley_norm) h
            first | parley_subst s1_1_w | parley_subst s1_1
        _ = x ^ (2 * n) * x ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := x) (m := 2 * n) (n := 2)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := x) (m := 2 * n) (n := 2)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := x) (m := 2 * n) (n := 2)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := x) (m := 2 * n) (n := 2)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := x) (m := 2 * n) (n := 2))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := x) (m := 2 * n) (n := 2)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := x) (m := 2 * n) (n := 2)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := x) (m := 2 * n) (n := 2)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := x) (m := 2 * n) (n := 2)); parley_set_side)
    -- 1.3. mun:square-nonneg
    have s1_3 : x ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_set_side)
    -- 1.4. inequalities, from 1.3
    have s1_4 : 1 + x ^ 2 > 0 := by parley_order
    -- 1.5. D3, from K1
    have s1_5 : h x = x ^ (2 * (n + 1)) / (1 + x ^ 2) := by parley_set_side
    -- 1.6. calculation
    have r461_1 : 1 + x ^ 2 ≠ 0 := by parley_set_side
    have s1_6 : h x = f x - g x := by
      calc h x = x ^ (2 * (n + 1)) / (1 + x ^ 2) := by parley_set_side
        _ = x ^ (2 * n) - x ^ (2 * n) / (1 + x ^ 2) := by linear_combination (norm := parley_field) ((1) / ((x ^ 2 + 1))) * s1_2
        _ = f x - g x := by parley_ring
    all_goals exact s1_6
  -- 2. D1
  have s2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), f x = x ^ (2 * n) := by parley_set_side
  -- 3. D2
  have s3 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), g x = x ^ (2 * n) / (1 + x ^ 2) := by parley_set_side
  -- 4. mun:interval-real
  have s4 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))) | exact ((Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))) | (have h := (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))); parley_set_side)
  -- 5. membership, from D1
  have s5 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 6. membership, from D2
  have r480_1 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), x ^ 2 ≥ 0 := by intro x h_x; (first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_set_side))
  have r480_2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), 1 + x ^ 2 > 0 := by intro x h_x; (parley_order)
  have s6 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 7. membership, from D3
  have r485_1 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), x ^ 2 ≥ 0 := by intro x h_x; (first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_set_side))
  have r485_2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), 1 + x ^ 2 > 0 := by intro x h_x; (parley_order)
  have s7 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 8. mun:function-into, from 5
  have s8 : Set.MapsTo f (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 9. mun:function-into, from 6
  have s9 : Set.MapsTo g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 10. mun:function-into, from 7
  have s10 : Set.MapsTo h (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 11. thm:continuous-power D := [0, 1], n := 2n, from 2, 4, 8
  have s11 : ContinuousOn f (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s4 (n := 2 * n) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_continuous_power (g := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s4 (n := 2 * n) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s4 (n := 2 * n) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s4 (n := 2 * n) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s4 (n := 2 * n) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 12. thm:integrand-continuous, from 3, 9
  have s12 : ContinuousOn g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := n) (g := g) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := n) (g := g) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := n) (g := g) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := n) (g := g) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := n) (g := g) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 13. arithmetic
  have s13 : (0 : ℤ) < 1 := by parley_arith
  -- 14. D1
  have s14 : (∫ t in 0..1, (f t : ℝ)) = (∫ t in 0..1, (t ^ (2 * n) : ℝ)) := by parley_set_side
  -- 15. calculation
  have s15 : (∫ t in 0..1, (f t : ℝ)) = 1 / (2 * (n : ℝ) + 1) := by
    calc (∫ t in 0..1, (f t : ℝ)) = (∫ t in 0..1, (t ^ (2 * n) : ℝ)) := by parley_set_side
      _ = 1 / (2 * (n : ℝ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n)) | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n)) | exact_mod_cast ((Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n))).symm | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n)); parley_set_side)
  -- 16. D0, from D3
  have s16 : (∫ t in 0..1, (t ^ (2 * (n + 1)) / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (h t : ℝ)) := by parley_set_side
  -- 17. D0, from D2
  have s17 : (∫ t in 0..1, (t ^ (2 * n) / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (g t : ℝ)) := by parley_set_side
  -- 18. calculation
  have s18 : (∫ t in 0..1, (t ^ (2 * (n + 1)) / (1 + t ^ 2) : ℝ)) = 1 / (2 * (n : ℝ) + 1) - (∫ t in 0..1, (t ^ (2 * n) / (1 + t ^ 2) : ℝ)) := by
    calc (∫ t in 0..1, (t ^ (2 * (n + 1)) / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (h t : ℝ)) := by parley_set_side
      _ = (∫ t in 0..1, (f t : ℝ)) - (∫ t in 0..1, (g t : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := f) (g := g) (h := h) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := f) (g := g) (h := h) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := f) (g := g) (h := h) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := f) (g := g) (h := h) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.thm_integral_difference (f := f) (g := g) (h := h) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := f) (g := g) (h := h) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := f) (g := g) (h := h) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := f) (g := g) (h := h) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := f) (g := g) (h := h) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
      _ = 1 / (2 * (n : ℝ) + 1) - (∫ t in 0..1, (g t : ℝ)) := by parley_subst s15
      _ = 1 / (2 * (n : ℝ) + 1) - (∫ t in 0..1, (t ^ (2 * n) / (1 + t ^ 2) : ℝ)) := by parley_subst s17
  all_goals exact s18

end Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence
