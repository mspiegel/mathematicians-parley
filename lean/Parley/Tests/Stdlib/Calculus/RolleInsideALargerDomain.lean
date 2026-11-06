module

public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.RolleInsideALargerDomain

theorem rolle_inside_a_larger_domain (a : ℝ) (b : ℝ) (hH3 : a < b) (h : ℝ → ℝ) (hH5 : ContinuousOn h (Set.Icc a b : Set ℝ)) (hH6 : ∀ x ∈ (Set.Ioo a b : Set ℝ), DifferentiableAt ℝ h x) (hH7 : h a = h b) :
    (∃ c ∈ (Set.Ioo a b : Set ℝ), (deriv h) c = 0) := by
  -- 1. mun:interval-real
  have s1 : (Set.Icc a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b)); parley_set_side)
  -- 2. mun:subset-self X := ℝ
  have s2 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))); parley_set_side)
  -- 3. thm:rolle-on-part D := ℝ, f := h, from H3, H5, H6, H7, 1, 2
  have s3 : ∃ c ∈ (Set.Ioo a b : Set ℝ), (deriv h) c = 0 := by first | exact (Parley.Items.Stdlib.Calculus.thm_rolle_on_part (f := h) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (a := a) (b := b) hH3 (by parley_whole_side) hH5 (by parley_whole_side) hH7) | exact ((Parley.Items.Stdlib.Calculus.thm_rolle_on_part (f := h) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (a := a) (b := b) hH3 (by parley_whole_side) hH5 (by parley_whole_side) hH7)).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_rolle_on_part (f := h) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (a := a) (b := b) hH3 (by parley_whole_side) hH5 (by parley_whole_side) hH7) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_rolle_on_part (f := h) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (a := a) (b := b) hH3 (by parley_whole_side) hH5 (by parley_whole_side) hH7) | (have h := (Parley.Items.Stdlib.Calculus.thm_rolle_on_part (f := h) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (a := a) (b := b) hH3 (by parley_whole_side) hH5 (by parley_whole_side) hH7); parley_set_side)
  all_goals exact s3

end Parley.Tests.Stdlib.Calculus.RolleInsideALargerDomain
