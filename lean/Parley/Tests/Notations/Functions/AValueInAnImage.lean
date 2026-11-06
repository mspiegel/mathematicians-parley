module

public import PowerTactics
public import RealTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.AValueInAnImage

theorem a_value_in_an_image (f : ℝ → ℝ) (hH2 : ∀ x : ℝ, f x = 2 * x + 1) :
    (3 : ℝ) ∈ f '' ((Set.univ : Set ℝ) ∩ ({(1 : ℝ), (2 : ℝ)} : Set ℝ)) := by
  -- 1. inspection
  have s1 : (1 : ℤ) ∈ ({(1 : ℤ), (2 : ℤ)} : Set ℤ) := by parley_set_side
  -- 2. mun:pair-subset a := 1, b := 2, X := ℝ
  have s2 : ({(1 : ℝ), (2 : ℝ)} : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_pair_subset (X := (Set.univ : Set ℝ)) (a := (1 : ℝ)) (b := (2 : ℝ)) (by parley_whole_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Sets.mun_pair_subset (X := (Set.univ : Set ℝ)) (a := (1 : ℝ)) (b := (2 : ℝ)) (by parley_whole_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_pair_subset (X := (Set.univ : Set ℝ)) (a := (1 : ℝ)) (b := (2 : ℝ)) (by parley_whole_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_pair_subset (X := (Set.univ : Set ℝ)) (a := (1 : ℝ)) (b := (2 : ℝ)) (by parley_whole_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_pair_subset (X := (Set.univ : Set ℝ)) (a := (1 : ℝ)) (b := (2 : ℝ)) (by parley_whole_side) (by parley_whole_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_pair_subset (X := (Set.univ : Set ℝ)) (a := (1 : ℝ)) (b := (2 : ℝ)) (by parley_whole_side) (by parley_whole_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sets.mun_pair_subset (X := (Set.univ : Set ℝ)) (a := (1 : ℝ)) (b := (2 : ℝ)) (by parley_whole_side) (by parley_whole_side)); parley_set_side)
  -- 3. mun:value-in-image, from 1, 2
  have s3 : f 1 ∈ f '' ((Set.univ : Set ℝ) ∩ ({(1 : ℝ), (2 : ℝ)} : Set ℝ)) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ), (2 : ℝ)} : Set ℝ)) (f := f) (s := (1 : ℝ)) (W := Set.univ) (by parley_whole_side) s1 (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ), (2 : ℝ)} : Set ℝ)) (f := f) (s := (1 : ℝ)) (W := Set.univ) (by parley_whole_side) s1 (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ), (2 : ℝ)} : Set ℝ)) (f := f) (s := (1 : ℝ)) (W := Set.univ) (by parley_whole_side) s1 (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ), (2 : ℝ)} : Set ℝ)) (f := f) (s := (1 : ℝ)) (W := Set.univ) (by parley_whole_side) s1 (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ), (2 : ℝ)} : Set ℝ)) (f := f) (s := (1 : ℝ)) (W := Set.univ) (by parley_whole_side) s1 (by parley_whole_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ), (2 : ℝ)} : Set ℝ)) (f := f) (s := (1 : ℝ)) (W := Set.univ) (by parley_whole_side) s1 (by parley_whole_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℝ)) (Y := ({(1 : ℝ), (2 : ℝ)} : Set ℝ)) (f := f) (s := (1 : ℝ)) (W := Set.univ) (by parley_whole_side) s1 (by parley_whole_side)); parley_set_side)
  -- 4. instantiate x := 1 in H2
  have s4 : f 1 = 2 * 1 + 1 := by first | linear_combination (norm := parley_norm) (hH2 (1 : ℝ)) | (have h := (hH2 (1 : ℝ)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 (1 : ℝ)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 (1 : ℝ)) | exact_mod_cast ((hH2 (1 : ℝ))).symm | (have h := (hH2 (1 : ℝ)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (1 : ℝ)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (1 : ℝ)); parley_int_power h) | (have h := (hH2 (1 : ℝ)); parley_rat_of_real h) | (have h := (hH2 (1 : ℝ)); parley_set_side)
  -- 5. calculation
  have s5 : f 1 = 3 := by
    calc f 1 = 2 * 1 + 1 := by parley_set_side
      _ = 3 := by norm_num
  -- 6. substitute f(1) = 3 (line 5) into line 3
  have s6 : (3 : ℝ) ∈ f '' ((Set.univ : Set ℝ) ∩ ({(1 : ℝ), (2 : ℝ)} : Set ℝ)) := by parley_subst_at s5 s3
  all_goals exact s6

end Parley.Tests.Notations.Functions.AValueInAnImage
