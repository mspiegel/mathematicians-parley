module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import PowerTactics
public import RealTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous
public import Parley.Proofs.Wiedijk.Leibniz.PowerIntegral

/-! Written from proofs/wiedijk/leibniz.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Leibniz.IntegralBounds

set_option maxHeartbeats 800000 in
theorem integral_bounds (n : ℤ) (hH1 : 0 ≤ n) :
    True ∧ (∫ t in 0..1, (t ^ (2 * n).toNat / (1 + t ^ 2) : ℝ)) ≥ 0 ∧ (∫ t in 0..1, (t ^ (2 * n).toNat / (1 + t ^ 2) : ℝ)) ≤ 1 / (2 * (n : ℝ) + 1) := by
  set f : ℝ → ℝ := fun x => x ^ (2 * n).toNat with hD1
  set g : ℝ → ℝ := fun x => x ^ (2 * n).toNat / (1 + x ^ 2) with hD2
  -- 1. mun:interval-real
  have s1 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))) | exact ((Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))) | (have h := (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))); parley_set_side)
  -- 2. D1
  have s2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), f x = x ^ (2 * n).toNat := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
  -- 3. D2
  have s3 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), g x = x ^ (2 * n).toNat / (1 + x ^ 2) := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_set_side
  -- 4. membership, from D1
  have s4 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 5. membership, from D2
  have r556_1 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), x ^ 2 ≥ 0 := by intro x h_x; (first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_set_side))
  have r556_2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), 1 + x ^ 2 > 0 := by intro x h_x; (parley_order)
  have s5 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 6. mun:function-into, from 4
  have s6 : Set.MapsTo f (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 7. mun:function-into, from 5
  have s7 : Set.MapsTo g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 8. thm:continuous-power D := [0, 1], n := 2n, from 1, 2, 6
  have s8 : ContinuousOn f (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (n := 2 * n) (by parley_set_side) s2) | exact ((Parley.Items.Stdlib.Calculus.thm_continuous_power (g := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (n := 2 * n) (by parley_set_side) s2)).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (n := 2 * n) (by parley_set_side) s2) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (n := 2 * n) (by parley_set_side) s2) | (have h := (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (n := 2 * n) (by parley_set_side) s2); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (n := 2 * n) (by parley_set_side) s2); parley_set_side)
  -- 9. thm:integrand-continuous, from 3, 7
  have s9 : ContinuousOn g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := n) (by parley_set_side) (g := g) (by parley_set_side) s3) | exact ((Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := n) (by parley_set_side) (g := g) (by parley_set_side) s3)).symm | simpa using (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := n) (by parley_set_side) (g := g) (by parley_set_side) s3) | exact_mod_cast (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := n) (by parley_set_side) (g := g) (by parley_set_side) s3) | (have h := (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := n) (by parley_set_side) (g := g) (by parley_set_side) s3); parley_set_side)
  -- 10. proof
  have s10 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), g x ≥ 0 := by
    intro x hK1
    -- 10.1. def:interval a := 0, b := 1, from K1
    have s10_1 : x ≥ 0 := by first | linarith [((Parley.Items.Stdlib.Calculus.def_interval (x := x) (a := (0 : ℝ)) (b := (1 : ℝ)))).mp (by parley_set_side)] | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := x) (a := (0 : ℝ)) (b := (1 : ℝ)))).mp (by parley_set_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_interval (x := x) (a := (0 : ℝ)) (b := (1 : ℝ)))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := x) (a := (0 : ℝ)) (b := (1 : ℝ)))).mp (by parley_set_side); parley_set_side)
    -- 10.2. mun:power-nonneg a := x, m := 2n, from 10.1
    have s10_2 : x ^ (2 * n).toNat ≥ 0 := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nonneg (a := x) (m := 2 * n) (by parley_set_side) (by parley_set_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_power_nonneg (a := x) (m := 2 * n) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nonneg (a := x) (m := 2 * n) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nonneg (a := x) (m := 2 * n) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nonneg (a := x) (m := 2 * n) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 10.3. mun:square-nonneg
    have s10_3 : x ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_set_side)
    -- 10.4. inequalities, from 10.3
    have s10_4 : 1 + x ^ 2 > 0 := by parley_order
    -- 10.5. mun:quotient-nonneg x := x^(2n), y := 1 + x², from 10.2, 10.4
    have s10_5 : x ^ (2 * n).toNat / (1 + x ^ 2) ≥ 0 := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := x ^ (2 * n).toNat) (y := 1 + x ^ 2) (by parley_set_side) (by parley_set_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := x ^ (2 * n).toNat) (y := 1 + x ^ 2) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := x ^ (2 * n).toNat) (y := 1 + x ^ 2) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := x ^ (2 * n).toNat) (y := 1 + x ^ 2) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := x ^ (2 * n).toNat) (y := 1 + x ^ 2) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 10.6. D2, from K1
    have s10_6 : g x = x ^ (2 * n).toNat / (1 + x ^ 2) := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_set_side
    -- 10.7. transitivity, from 10.6, 10.5
    have r597_1 : 1 + x ^ 2 ≠ 0 := by parley_set_side
    have s10_7 : g x ≥ 0 := by parley_order
    all_goals exact s10_7
  -- 11. proof
  have s11 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), g x ≤ f x := by
    intro x hK2
    -- 11.1. def:interval a := 0, b := 1, from K2
    have s11_1 : x ≥ 0 := by first | linarith [((Parley.Items.Stdlib.Calculus.def_interval (x := x) (a := (0 : ℝ)) (b := (1 : ℝ)))).mp (by parley_set_side)] | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := x) (a := (0 : ℝ)) (b := (1 : ℝ)))).mp (by parley_set_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_interval (x := x) (a := (0 : ℝ)) (b := (1 : ℝ)))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := x) (a := (0 : ℝ)) (b := (1 : ℝ)))).mp (by parley_set_side); parley_set_side)
    -- 11.2. mun:power-nonneg a := x, m := 2n, from 11.1
    have s11_2 : x ^ (2 * n).toNat ≥ 0 := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nonneg (a := x) (m := 2 * n) (by parley_set_side) (by parley_set_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_power_nonneg (a := x) (m := 2 * n) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nonneg (a := x) (m := 2 * n) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nonneg (a := x) (m := 2 * n) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nonneg (a := x) (m := 2 * n) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 11.3. mun:square-nonneg
    have s11_3 : x ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_set_side)
    -- 11.4. inequalities, from 11.3
    have s11_4 : 1 ≤ 1 + x ^ 2 := by parley_order
    -- 11.5. inequalities, from 11.3
    have s11_5 : 1 + x ^ 2 > 0 := by parley_order
    -- 11.6. mun:quotients-compared x := x^(2n), y := 1 + x², z := x^(2n), w := 1, from 11.2, 11.4
    have r620_1 : x ^ (2 * n).toNat ≤ x ^ (2 * n).toNat := by parley_order
    have r620_2 : (0 : ℤ) < 1 := by parley_arith
    have s11_6 : x ^ (2 * n).toNat / (1 + x ^ 2) ≤ x ^ (2 * n).toNat / 1 := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_quotients_compared (x := x ^ (2 * n).toNat) (y := 1 + x ^ 2) (z := x ^ (2 * n).toNat) (w := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_quotients_compared (x := x ^ (2 * n).toNat) (y := 1 + x ^ 2) (z := x ^ (2 * n).toNat) (w := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotients_compared (x := x ^ (2 * n).toNat) (y := 1 + x ^ 2) (z := x ^ (2 * n).toNat) (w := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotients_compared (x := x ^ (2 * n).toNat) (y := 1 + x ^ 2) (z := x ^ (2 * n).toNat) (w := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotients_compared (x := x ^ (2 * n).toNat) (y := 1 + x ^ 2) (z := x ^ (2 * n).toNat) (w := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 11.7. D2, from K2
    have s11_7 : g x = x ^ (2 * n).toNat / (1 + x ^ 2) := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_set_side
    -- 11.8. algebra, from D1, K2
    have s11_8 : x ^ (2 * n).toNat / 1 = f x := by parley_ring
    -- 11.9. transitivity, from 11.7, 11.6, 11.8
    have r631_1 : 1 + x ^ 2 ≠ 0 := by parley_set_side
    have s11_9 : g x ≤ f x := by parley_order
    all_goals exact s11_9
  -- 12. arithmetic
  have s12 : (0 : ℤ) < 1 := by parley_arith
  -- 13. thm:integral-nonneg a := 0, b := 1, f := g, from 7, 9, 10, 12
  have s13 : (∫ t in 0..1, (g t : ℝ)) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Calculus.thm_integral_nonneg (f := g) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_nonneg (f := g) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_integral_nonneg (f := g) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_nonneg (f := g) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 14. thm:integral-order a := 0, b := 1, f := g, g := f, from 6, 7, 8, 9, 11, 12
  have s14 : (∫ t in 0..1, (g t : ℝ)) ≤ (∫ t in 0..1, (f t : ℝ)) := by first | linarith [(Parley.Items.Stdlib.Calculus.thm_integral_order (f := g) (g := f) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_order (f := g) (g := f) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_integral_order (f := g) (g := f) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_order (f := g) (g := f) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 15. thm:power-integral m := 2n
  have s15 : (∫ t in 0..1, (t ^ (2 * n).toNat : ℝ)) = 1 / (2 * (n : ℝ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n) (by parley_set_side)) | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n) (by parley_set_side)) | exact_mod_cast ((Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n) (by parley_set_side))).symm | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n) (by parley_set_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n) (by parley_set_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n) (by parley_set_side)); parley_set_side)
  -- 16. D1
  have s16 : (∫ t in 0..1, (f t : ℝ)) = (∫ t in 0..1, (t ^ (2 * n).toNat : ℝ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
  -- 17. D0, from D2
  have s17 : (∫ t in 0..1, (t ^ (2 * n).toNat / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (g t : ℝ)) := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_set_side
  -- 18. def:interval a := 0, b := 1, x := 1
  have r653_1 : (0 : ℤ) ≤ 1 := by parley_arith
  have r653_2 : (1 : ℤ) ≤ 1 := by parley_arith
  have s18 : (1 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := (1 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := (1 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr (by parley_set_side); parley_set_side)
  -- 19. mun:integral-real a := 0, b := 1, f := g, x := 1, from 7, 9, 12, 18
  -- 20. substitute J(n) = ∫(0 to 1) g(t) dt (line 17) into line 19
  -- 21. transitivity, from 17, 13
  have s21 : (∫ t in 0..1, (t ^ (2 * n).toNat / (1 + t ^ 2) : ℝ)) ≥ 0 := by parley_order
  -- 22. transitivity, from 17, 14, 16, 15
  have r668_2 : 0 < 2 * n + 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := 2 * n) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := 2 * n) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := 2 * n) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := 2 * n) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := 2 * n) (by parley_set_side)); parley_set_side)
  have s22 : (∫ t in 0..1, (t ^ (2 * n).toNat / (1 + t ^ 2) : ℝ)) ≤ 1 / (2 * (n : ℝ) + 1) := by parley_order
  -- 23. join 20, 21, 22
  have s23a : (∫ t in 0..1, (t ^ (2 * n).toNat / (1 + t ^ 2) : ℝ)) ≥ 0 := by parley_set_side
  have s23b : (∫ t in 0..1, (t ^ (2 * n).toNat / (1 + t ^ 2) : ℝ)) ≤ 1 / (2 * (n : ℝ) + 1) := by parley_set_side
  exact ⟨by parley_set_side, by parley_set_side, by parley_set_side⟩

end Parley.Proofs.Wiedijk.Leibniz.IntegralBounds
