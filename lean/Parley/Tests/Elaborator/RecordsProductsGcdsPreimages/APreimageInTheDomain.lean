module

public import SetTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.APreimageInTheDomain

theorem a_preimage_in_the_domain (f : ℝ → ℝ) (B : Set ℝ) (hH2 : B ⊆ (Set.univ : Set ℝ)) :
    (Set.univ : Set ℝ) ∩ f ⁻¹' B ⊆ (Set.univ : Set ℝ) := by
  -- 1. mun:preimage-within X := ℝ, W := ℝ, Z := B
  have s1 : (Set.univ : Set ℝ) ∩ f ⁻¹' B ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_preimage_within (X := (Set.univ : Set ℝ)) (Z := B) (f := f) (W := Set.univ) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_preimage_within (X := (Set.univ : Set ℝ)) (Z := B) (f := f) (W := Set.univ) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_preimage_within (X := (Set.univ : Set ℝ)) (Z := B) (f := f) (W := Set.univ) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_preimage_within (X := (Set.univ : Set ℝ)) (Z := B) (f := f) (W := Set.univ) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_preimage_within (X := (Set.univ : Set ℝ)) (Z := B) (f := f) (W := Set.univ) (by parley_whole_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.APreimageInTheDomain
