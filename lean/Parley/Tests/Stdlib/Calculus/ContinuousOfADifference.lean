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

namespace Parley.Tests.Stdlib.Calculus.ContinuousOfADifference

theorem continuous_of_a_difference (f : ℝ → ℝ) (hH2 : ContinuousOn f (Set.univ : Set ℝ)) (g : ℝ → ℝ) (hH4 : ContinuousOn g (Set.univ : Set ℝ)) (F : ℝ → ℝ) (hH6 : ∀ x : ℝ, F x = f x - g x) :
    ContinuousOn F (Set.univ : Set ℝ) := by
  -- 1. mun:subset-self X := ℝ
  have s1 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ))); parley_set_side)
  -- 2. thm:continuous-difference D := ℝ, from H2, H4, H6, 1
  have s2 : ContinuousOn F (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.thm_continuous_difference (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_continuous_difference (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_continuous_difference (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_continuous_difference (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_continuous_difference (F := F) (f := f) (g := g) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
  all_goals exact s2

end Parley.Tests.Stdlib.Calculus.ContinuousOfADifference
