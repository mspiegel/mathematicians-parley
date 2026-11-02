module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/image-of-affine-map.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ImageOfAffineMap.ImageOfAffineMap

theorem image_of_affine_map (f : ℤ → ℤ) (hH2 : ∀ x : ℤ, f x = 4 * x + 5) :
    f '' (Set.univ : Set ℤ) = (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) := by
  -- 1. mun:subset-self
  have s1 : (Set.univ : Set ℤ) ⊆ (Set.univ : Set ℤ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℤ))) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℤ)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℤ))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℤ))) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℤ))); parley_set_side)
  -- 2. proof
  have s2 : ∀ y ∈ f '' (Set.univ : Set ℤ), y ∈ (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) := by
    intro y hK1
    -- 2.1. obtain s: def:image u := y, Y := ℤ, from K1, 1
    obtain ⟨s, _, s2_1⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (u := y) (W := Set.univ) (by parley_set_side) (by parley_set_side))).mp (by parley_set_side)
    -- 2.2. instantiate x := s in H2
    have s2_2 : f s = 4 * s + 5 := by first | linear_combination (norm := parley_norm) (hH2 s) | (have h := (hH2 s); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 s); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 s) | exact_mod_cast ((hH2 s)).symm | (have h := (hH2 s); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 s); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 s); parley_int_power h) | (have h := (hH2 s); parley_set_side)
    -- 2.3. algebra, from 2.1, 2.2
    have s2_3 : y = 4 * (s + 1) + 1 := by linear_combination (norm := parley_norm) s2_1 + s2_2
    -- 2.4. exhibit, from 2.3
    have s2_4 : ∃ k : ℤ, y = 4 * k + 1 := ⟨s + 1, by parley_set_side⟩
    -- 2.5. def:set-image u := y, from 2.4
    have s2_5 : y ∈ (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun k : ℤ => 4 * k + 1)) (Y := (Set.univ : Set ℤ)) (u := y) (Z := Set.univ) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun k : ℤ => 4 * k + 1)) (Y := (Set.univ : Set ℤ)) (u := y) (Z := Set.univ) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
    all_goals parley_set_side
  -- 3. def:subset, from 2
  have s3 : f '' (Set.univ : Set ℤ) ⊆ (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := f '' (Set.univ : Set ℤ)) (Y := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := f '' (Set.univ : Set ℤ)) (Y := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)))).mpr (by parley_set_side); parley_set_side)
  -- 4. proof
  have s4 : ∀ y ∈ (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ), y ∈ f '' (Set.univ : Set ℤ) := by
    intro y hK2
    -- 4.1. obtain m: def:set-image u := y, from K2
    obtain ⟨m, _, s4_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun k : ℤ => 4 * k + 1)) (Y := (Set.univ : Set ℤ)) (u := y) (Z := Set.univ) (by parley_set_side))).mp (by parley_set_side)
    -- 4.2. instantiate x := m − 1 in H2
    have s4_2 : f (m - 1) = 4 * (m - 1) + 5 := by first | linear_combination (norm := parley_norm) (hH2 (m - 1)) | (have h := (hH2 (m - 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH2 (m - 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH2 (m - 1)) | exact_mod_cast ((hH2 (m - 1))).symm | (have h := (hH2 (m - 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (m - 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH2 (m - 1)); parley_int_power h) | (have h := (hH2 (m - 1)); parley_set_side)
    -- 4.3. mun:value-in-image Y := ℤ, s := m − 1, from 1
    have s4_3 : f (m - 1) ∈ f '' (Set.univ : Set ℤ) := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (s := m - 1) (W := Set.univ) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (s := m - 1) (W := Set.univ) (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (s := m - 1) (W := Set.univ) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (s := m - 1) (W := Set.univ) (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℤ)) (f := f) (s := m - 1) (W := Set.univ) (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
    -- 4.4. substitute
    have s4_4 : y ∈ f '' (Set.univ : Set ℤ) := by
      have c1 : f (m - 1) = y := by linear_combination (norm := parley_norm) (-1) * s4_1 + s4_2
      have row1 : y ∈ f '' (Set.univ : Set ℤ) := by parley_subst_at c1 s4_3
      exact row1
    all_goals parley_set_side
  -- 5. def:subset, from 4
  have s5 : (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) ⊆ f '' (Set.univ : Set ℤ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)) (Y := f '' (Set.univ : Set ℤ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)) (Y := f '' (Set.univ : Set ℤ)))).mpr (by parley_set_side); parley_set_side)
  -- 6. mun:subset-antisymmetric, from 3, 5
  have s6 : f '' (Set.univ : Set ℤ) = (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' (Set.univ : Set ℤ)) (Y := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' (Set.univ : Set ℤ)) (Y := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' (Set.univ : Set ℤ)) (Y := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' (Set.univ : Set ℤ)) (Y := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' (Set.univ : Set ℤ)) (Y := (fun k : ℤ => 4 * k + 1) '' (Set.univ : Set ℤ)) (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals parley_set_side

end Parley.Proofs.Hammack.ImageOfAffineMap.ImageOfAffineMap
