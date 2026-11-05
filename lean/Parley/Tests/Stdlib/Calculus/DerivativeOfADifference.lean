module

public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.DerivativeOfADifference

theorem derivative_of_a_difference (f : ℝ → ℝ) (hH2 : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ f x) (g : ℝ → ℝ) (hH4 : ∀ x : ℝ, g x = 3 * x) (F : ℝ → ℝ) (hH6 : ∀ x : ℝ, F x = f x - g x) :
    (∀ x : ℝ, (deriv F) x = (deriv f) x - 3) := by
  -- 1. mun:subset-self X := ℝ
  have s1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))); parley_set_side)
  -- 2. mun:reals-open
  have s2 : IsOpen (Set.univ : Set ℝ) := by first | exact Parley.Items.Stdlib.Calculus.mun_reals_open | exact (Parley.Items.Stdlib.Calculus.mun_reals_open).symm | simpa using Parley.Items.Stdlib.Calculus.mun_reals_open | exact_mod_cast Parley.Items.Stdlib.Calculus.mun_reals_open | (have h := Parley.Items.Stdlib.Calculus.mun_reals_open; parley_set_side)
  -- 3. thm:derivative-linear D := ℝ, U := ℝ, m := 3, from H4, 1, 2
  have s3 : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ g x := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
  -- 4. thm:derivative-linear D := ℝ, U := ℝ, m := 3, from H4, 1, 2
  have s4 : ∀ x : ℝ, (deriv g) x = 3 := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (m := (3 : ℝ)) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
  -- 5. thm:derivative-difference D := ℝ, U := ℝ, from H2, H6, 1, 3
  have s5 : ∀ x : ℝ, (deriv F) x = (deriv f) x - (deriv g) x := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
  -- 6. proof
  have s6 : ∀ x : ℝ, (deriv F) x = (deriv f) x - 3 := by
    intro x
    -- 6.1. instantiate x := x in line 5
    have s6_1 : (deriv F) x = (deriv f) x - (deriv g) x := by first | linear_combination (norm := parley_norm) (s5 x) | (have h := (s5 x); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s5 x); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s5 x) | exact_mod_cast ((s5 x)).symm | (have h := (s5 x); rify; linear_combination (norm := parley_norm) h) | (have h := (s5 x); qify; linear_combination (norm := parley_norm) h) | (have h := (s5 x); parley_int_power h) | (have h := (s5 x); parley_set_side)
    -- 6.2. substitute
    have s6_2 : (deriv F) x = (deriv f) x - 3 := by
      have c1 : (deriv g) x = 3 := by first | linear_combination (norm := parley_norm) (s4 x) | (have h := (s4 x); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s4 x); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s4 x) | exact_mod_cast ((s4 x)).symm | (have h := (s4 x); rify; linear_combination (norm := parley_norm) h) | (have h := (s4 x); qify; linear_combination (norm := parley_norm) h) | (have h := (s4 x); parley_int_power h) | (have h := (s4 x); parley_set_side)
      have row1 : (deriv F) x = (deriv f) x - 3 := by parley_subst_at c1 s6_1
      exact row1
    all_goals exact s6_2
  all_goals exact s6

end Parley.Tests.Stdlib.Calculus.DerivativeOfADifference
