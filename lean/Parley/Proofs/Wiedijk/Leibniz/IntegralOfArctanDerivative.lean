module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import PowerTactics
public import RealTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Trigonometry
public import Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus
public import Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous

/-! Written from proofs/wiedijk/leibniz.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Leibniz.IntegralOfArctanDerivative

set_option maxHeartbeats 600000 in
theorem integral_of_arctan_derivative :
    (∫ t in 0..1, (t ^ (2 * 0) / (1 + t ^ 2) : ℝ)) = Real.pi / 4 := by
  set g : ℝ → ℝ := fun x => x ^ (2 * 0) / (1 + x ^ 2) with hD1
  set F : ℝ → ℝ := fun x => Real.arctan x with hD2
  -- 1. mun:interval-real
  have s1 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))) | exact ((Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))) | (have h := (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ))); parley_set_side)
  -- 2. D1
  have s2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), g x = x ^ (2 * 0) / (1 + x ^ 2) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
  -- 3. D2
  have s3 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), F x = Real.arctan x := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_set_side
  -- 4. mun:arctan-real, from D2
  have s4 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; (first | exact (Parley.Items.Stdlib.Trigonometry.mun_arctan_real (x := x)) | exact ((Parley.Items.Stdlib.Trigonometry.mun_arctan_real (x := x))).symm | simpa using (Parley.Items.Stdlib.Trigonometry.mun_arctan_real (x := x)) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_arctan_real (x := x)) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_arctan_real (x := x)); parley_set_side))
  -- 5. mun:function-into, from 4
  have s5 : Set.MapsTo F (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 6. proof
  have s6 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by
    intro x hK1
    -- 6.1. mun:square-nonneg
    have s6_1 : x ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_set_side)
    -- 6.2. membership, from D1, K1
    have r339_1 : 1 + x ^ 2 > 0 := by parley_order
    all_goals parley_set_side
  -- 7. mun:function-into, from 6
  have s7 : Set.MapsTo g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 8. thm:integrand-continuous n := 0, from 2, 7
  have s8 : ContinuousOn g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := (0 : ℤ)) (by parley_set_side) (g := g) (by parley_set_side) s2) | exact ((Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := (0 : ℤ)) (by parley_set_side) (g := g) (by parley_set_side) s2)).symm | simpa using (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := (0 : ℤ)) (by parley_set_side) (g := g) (by parley_set_side) s2) | exact_mod_cast (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := (0 : ℤ)) (by parley_set_side) (g := g) (by parley_set_side) s2) | (have h := (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := (0 : ℤ)) (by parley_set_side) (g := g) (by parley_set_side) s2); parley_set_side)
  -- 9. thm:continuous-arctan D := [0, 1], from 1, 3, 5
  have s9 : ContinuousOn F (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Items.Stdlib.Trigonometry.thm_continuous_arctan (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 s3) | exact ((Parley.Items.Stdlib.Trigonometry.thm_continuous_arctan (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 s3)).symm | simpa using (Parley.Items.Stdlib.Trigonometry.thm_continuous_arctan (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 s3) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_continuous_arctan (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 s3) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_continuous_arctan (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 s3); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_continuous_arctan (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 s3); parley_set_side)
  -- 10. thm:derivative-arctan D := [0, 1], U := (0, 1), from 1, 3, 5
  have r353_1 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))) | exact ((Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))); parley_set_side)
  have r353_2 : IsOpen (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))) | exact ((Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))); parley_set_side)
  have s10 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ F x := by first | exact (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_1 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (by parley_set_side) (by parley_set_side) s3) | exact ((Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_1 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (by parley_set_side) (by parley_set_side) s3)).symm | simpa using (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_1 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (by parley_set_side) (by parley_set_side) s3) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_1 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (by parley_set_side) (by parley_set_side) s3) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_1 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (by parley_set_side) (by parley_set_side) s3); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_1 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (by parley_set_side) (by parley_set_side) s3); parley_set_side)
  -- 11. thm:derivative-arctan D := [0, 1], U := (0, 1), from 1, 3, 5
  have r358_1 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))) | exact ((Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))); parley_set_side)
  have r358_2 : IsOpen (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))) | exact ((Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ))); parley_set_side)
  have s11 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (deriv F) x = 1 / (1 + x ^ 2) := by first | exact (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (by parley_set_side) (by parley_set_side) s3) | exact ((Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (by parley_set_side) (by parley_set_side) s3)).symm | simpa using (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (by parley_set_side) (by parley_set_side) s3) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (by parley_set_side) (by parley_set_side) s3) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (by parley_set_side) (by parley_set_side) s3); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 (by parley_set_side) (by parley_set_side) s3); parley_set_side)
  -- 12. proof
  have s12 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (deriv F) x = g x := by
    intro x hK2
    -- 12.1. mun:in-subset, from K2
    have r367_1 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))) | exact ((Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ))); parley_set_side)
    have s12_1 : x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (u := x) (by parley_set_side) hK2) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (u := x) (by parley_set_side) hK2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (u := x) (by parley_set_side) hK2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (u := x) (by parley_set_side) hK2) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (u := x) (by parley_set_side) hK2); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (u := x) (by parley_set_side) hK2); parley_set_side)
    -- 12.2. calculation
    have s12_2 : x ^ (2 * 0) = 1 := by
      calc x ^ (2 * 0) = x ^ 0 := by norm_num
        _ = 1 := by parley_ring
    -- 12.3. D1, from 12.1
    have s12_3 : g x = x ^ (2 * 0) / (1 + x ^ 2) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
    -- 12.4. calculation
    have s12_4 : (deriv F) x = g x := by
      calc (deriv F) x = 1 / (1 + x ^ 2) := by parley_set_side
        _ = x ^ (2 * 0) / (1 + x ^ 2) := by parley_subst s12_2
        _ = g x := by parley_set_side
    all_goals exact s12_4
  -- 13. arithmetic
  have s13 : (0 : ℤ) < 1 := by parley_arith
  -- 14. def:interval a := 0, b := 1, x := 0
  have r388_1 : (0 : ℤ) ≤ 0 := by parley_arith
  have r388_2 : (0 : ℤ) ≤ 1 := by parley_arith
  have s14 : (0 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := (0 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := (0 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr (by parley_set_side); parley_set_side)
  -- 15. def:interval a := 0, b := 1, x := 1
  have r393_1 : (0 : ℤ) ≤ 1 := by parley_arith
  have r393_2 : (1 : ℤ) ≤ 1 := by parley_arith
  have s15 : (1 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := (1 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := (1 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr (by parley_set_side); parley_set_side)
  -- 16. mun:arctan-values
  have s16a : Real.arctan (0 : ℝ) = 0 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1 | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1 | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1).symm | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1; parley_int_power h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1; parley_set_side)
  have s16b : Real.arctan (1 : ℝ) = Real.pi / 4 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2 | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2 | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2).symm | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2; parley_set_side)
  -- 17. D2, from 15
  have s17 : F 1 = Real.arctan (1 : ℝ) := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_set_side
  -- 18. D2, from 14
  have s18 : F 0 = Real.arctan (0 : ℝ) := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_set_side
  -- 19. calculation
  have s19 : F 1 = Real.pi / 4 := by
    calc F 1 = Real.arctan (1 : ℝ) := by parley_set_side
      _ = Real.pi / 4 := by parley_set_side
  -- 20. calculation
  have s20 : F 0 = 0 := by
    calc F 0 = Real.arctan (0 : ℝ) := by parley_set_side
      _ = 0 := by parley_set_side
  -- 21. D0, from D1
  have s21 : (∫ t in 0..1, (t ^ (2 * 0) / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (g t : ℝ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
  -- 22. calculation
  have s22 : (∫ t in 0..1, (t ^ (2 * 0) / (1 + t ^ 2) : ℝ)) = Real.pi / 4 := by
    calc (∫ t in 0..1, (t ^ (2 * 0) / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (g t : ℝ)) := by parley_set_side
      _ = F 1 - F 0 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus.fundamental_calculus (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (f := g) (by parley_set_side) (by parley_set_side) (F := F) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus.fundamental_calculus (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (f := g) (by parley_set_side) (by parley_set_side) (F := F) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus.fundamental_calculus (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (f := g) (by parley_set_side) (by parley_set_side) (F := F) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus.fundamental_calculus (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (f := g) (by parley_set_side) (by parley_set_side) (F := F) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast ((Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus.fundamental_calculus (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (f := g) (by parley_set_side) (by parley_set_side) (F := F) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | (have h := (Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus.fundamental_calculus (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (f := g) (by parley_set_side) (by parley_set_side) (F := F) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus.fundamental_calculus (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (f := g) (by parley_set_side) (by parley_set_side) (F := F) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus.fundamental_calculus (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (f := g) (by parley_set_side) (by parley_set_side) (F := F) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus.fundamental_calculus (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (f := g) (by parley_set_side) (by parley_set_side) (F := F) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_rat_of_real h) | (have h := (Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus.fundamental_calculus (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (f := g) (by parley_set_side) (by parley_set_side) (F := F) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
      _ = Real.pi / 4 - F 0 := by parley_subst s19
      _ = Real.pi / 4 := by parley_subst s20
  all_goals exact s22

end Parley.Proofs.Wiedijk.Leibniz.IntegralOfArctanDerivative
