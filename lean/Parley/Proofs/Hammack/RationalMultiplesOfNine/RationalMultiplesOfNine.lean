module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/rational-multiples-of-nine.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.RationalMultiplesOfNine.RationalMultiplesOfNine

theorem rational_multiples_of_nine :
    (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ) = (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ) := by
  -- 1. proof
  have s1 : ∀ t ∈ (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ), t ∈ (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ) := by
    intro t hK1
    -- 1.1. obtain m: def:set-image u := t, from K1
    obtain ⟨m, _, s1_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℚ => 9 * n)) (Y := (Set.univ : Set ℚ)) (u := t) (Z := Set.univ) (by parley_set_side))).mp (by parley_set_side)
    -- 1.2. algebra, from 1.1
    have s1_2 : t = 3 * (3 * m) := by linear_combination (norm := parley_norm) s1_1
    -- 1.3. exhibit, from 1.2
    have s1_3 : ∃ n : ℚ, t = 3 * n := ⟨3 * m, by parley_set_side⟩
    -- 1.4. def:set-image u := t, from 1.3
    have s1_4 : t ∈ (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℚ => 3 * n)) (Y := (Set.univ : Set ℚ)) (u := t) (Z := Set.univ) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℚ => 3 * n)) (Y := (Set.univ : Set ℚ)) (u := t) (Z := Set.univ) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s1_4
  -- 2. def:subset, from 1
  have s2 : (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ) ⊆ (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)))).mpr (by parley_set_side); parley_set_side)
  -- 3. proof
  have s3 : ∀ t ∈ (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ), t ∈ (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ) := by
    intro t hK2
    -- 3.1. obtain m: def:set-image u := t, from K2
    obtain ⟨m, _, s3_1⟩ := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℚ => 3 * n)) (Y := (Set.univ : Set ℚ)) (u := t) (Z := Set.univ) (by parley_set_side))).mp (by parley_set_side)
    -- 3.2. algebra, from 3.1
    have s3_2 : t = 9 * (m / 3) := by linear_combination (norm := parley_norm) ((3) / ((3))) * s3_1
    -- 3.3. exhibit, from 3.2
    have s3_3 : ∃ n : ℚ, t = 9 * n := ⟨m / 3, by parley_set_side⟩
    -- 3.4. def:set-image u := t, from 3.3
    have s3_4 : t ∈ (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℚ => 9 * n)) (Y := (Set.univ : Set ℚ)) (u := t) (Z := Set.univ) (by parley_set_side))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_set_image (E := (fun n : ℚ => 9 * n)) (Y := (Set.univ : Set ℚ)) (u := t) (Z := Set.univ) (by parley_set_side))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s3_4
  -- 4. def:subset, from 3
  have s4 : (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ) ⊆ (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)))).mpr (by parley_set_side); parley_set_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  have s5 : (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ) = (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)) s2 s4) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)) s2 s4)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)) s2 s4) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)) s2 s4) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (fun n : ℚ => 9 * n) '' (Set.univ : Set ℚ)) (Y := (fun n : ℚ => 3 * n) '' (Set.univ : Set ℚ)) s2 s4); parley_set_side)
  all_goals exact s5

end Parley.Proofs.Hammack.RationalMultiplesOfNine.RationalMultiplesOfNine
