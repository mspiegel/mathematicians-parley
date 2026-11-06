module

public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.ContinuousOnAPart

theorem continuous_on_a_part (f : ℝ → ℝ) (hH2 : ContinuousOn f (Set.univ : Set ℝ)) (S : Set ℝ) (hH3 : S ⊆ (Set.univ : Set ℝ)) :
    ContinuousOn f S := by
  -- 1. mun:subset-self X := ℝ
  have s1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))); parley_set_side)
  -- 2. mun:continuous-on-part D := ℝ, from H2, H3, 1
  have s2 : ContinuousOn f S := by first | exact (Parley.Items.Stdlib.Calculus.mun_continuous_on_part (f := f) (D := (Set.univ : Set ℝ)) (S := S) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Calculus.mun_continuous_on_part (f := f) (D := (Set.univ : Set ℝ)) (S := S) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_continuous_on_part (f := f) (D := (Set.univ : Set ℝ)) (S := S) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_continuous_on_part (f := f) (D := (Set.univ : Set ℝ)) (S := S) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Calculus.mun_continuous_on_part (f := f) (D := (Set.univ : Set ℝ)) (S := S) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
  all_goals exact s2

end Parley.Tests.Stdlib.Calculus.ContinuousOnAPart
