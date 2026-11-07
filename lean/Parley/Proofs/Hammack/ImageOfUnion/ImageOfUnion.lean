module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/image-of-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ImageOfUnion.ImageOfUnion

set_option maxHeartbeats 600000 in
theorem image_of_union {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B) (W : Set α) (hH4 : W ⊆ A) (X : Set α) (hH5 : X ⊆ A) :
    f '' (A ∩ (W ∪ X)) = f '' (A ∩ W) ∪ f '' (A ∩ X) := by
  -- 1. mun:union-subset, from H4, H5
  have s1 : W ∪ X ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := W) (Y := X) (Z := A) hH4 hH5)
  -- 2. proof
  have s2 : ∀ y ∈ f '' (A ∩ (W ∪ X)), y ∈ f '' (A ∩ W) ∪ f '' (A ∩ X) := by
    intro y hK1
    -- 2.1. obtain s: def:image u := y, Y := W ∪ X, from K1, 1
    obtain ⟨s, s2_1a, s2_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := W ∪ X) (f := f) (u := y) (W := Set.univ) s1 (by parley_set_side))).mp (by parley_set_side)
    -- 2.2. def:union u := s, Y := W, Z := X, from 2.1
    have s2_2 : s ∈ W ∨ s ∈ X := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := W) (Z := X) (u := s))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := W) (Z := X) (u := s))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := W) (Z := X) (u := s))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := W) (Z := X) (u := s))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := W) (Z := X) (u := s))).mp (by parley_set_side); parley_set_side)
    -- 2.3. cases, from 2.2
    have s2_3 : y ∈ f '' (A ∩ W) ∪ f '' (A ∩ X) := by
      rcases s2_2 with hC1 | hC2
      · skip
        -- 2.3.1. mun:value-in-image Y := W, from C1, H4
        have s2_3_1 : f s ∈ f '' (A ∩ W) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := W) (f := f) (s := s) (W := Set.univ) hH4 hC1 (by parley_set_side))
        -- 2.3.2. substitute y = f(s) (line 2.1) into line 2.3.1
        have s2_3_2 : y ∈ f '' (A ∩ W) := by parley_subst_at s2_1b s2_3_1
        -- 2.3.3. mun:in-union-left Y := f[W], Z := f[X], from 2.3.2
        have s2_3_3 : y ∈ f '' (A ∩ W) ∪ f '' (A ∩ X) := by exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := f '' (A ∩ W)) (Z := f '' (A ∩ X)) (u := y) s2_3_2)
        all_goals parley_set_side
      · skip
        -- 2.3.4. mun:value-in-image Y := X, from C2, H5
        have s2_3_4 : f s ∈ f '' (A ∩ X) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := s) (W := Set.univ) hH5 hC2 (by parley_set_side))
        -- 2.3.5. substitute y = f(s) (line 2.1) into line 2.3.4
        have s2_3_5 : y ∈ f '' (A ∩ X) := by parley_subst_at s2_1b s2_3_4
        -- 2.3.6. mun:in-union-right Y := f[W], Z := f[X], from 2.3.5
        have s2_3_6 : y ∈ f '' (A ∩ W) ∪ f '' (A ∩ X) := by exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := f '' (A ∩ W)) (Z := f '' (A ∩ X)) (u := y) s2_3_5)
        all_goals parley_set_side
    all_goals exact s2_3
  -- 3. def:subset, from 2
  have s3 : f '' (A ∩ (W ∪ X)) ⊆ f '' (A ∩ W) ∪ f '' (A ∩ X) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := f '' (A ∩ (W ∪ X))) (Y := f '' (A ∩ W) ∪ f '' (A ∩ X)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := f '' (A ∩ (W ∪ X))) (Y := f '' (A ∩ W) ∪ f '' (A ∩ X)))).mpr (by parley_set_side); parley_set_side)
  -- 4. proof
  have s4 : ∀ t ∈ W, t ∈ W ∪ X := by
    intro t hK2
    -- 4.1. mun:in-union-left Y := W, Z := X, from K2
    have s4_1 : t ∈ W ∪ X := by exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := W) (Z := X) (u := t) hK2)
    all_goals exact s4_1
  -- 5. def:subset, from 4
  have s5 : W ⊆ W ∪ X := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := W) (Y := W ∪ X))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := W) (Y := W ∪ X))).mpr (by parley_set_side); parley_set_side)
  -- 6. mun:image-monotone Y := W, Z := W ∪ X, from 5
  have s6 : f '' (A ∩ W) ⊆ f '' (A ∩ (W ∪ X)) := by exact (Parley.Items.Stdlib.Functions.mun_image_monotone (X := A) (Y := W) (Z := W ∪ X) (f := f) (W := Set.univ) s5 (by parley_set_side))
  -- 7. proof
  have s7 : ∀ t ∈ X, t ∈ W ∪ X := by
    intro t hK3
    -- 7.1. mun:in-union-right Y := W, Z := X, from K3
    have s7_1 : t ∈ W ∪ X := by exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := W) (Z := X) (u := t) hK3)
    all_goals exact s7_1
  -- 8. def:subset, from 7
  have s8 : X ⊆ W ∪ X := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := W ∪ X))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := X) (Y := W ∪ X))).mpr (by parley_set_side); parley_set_side)
  -- 9. mun:image-monotone Y := X, Z := W ∪ X, from 8
  have s9 : f '' (A ∩ X) ⊆ f '' (A ∩ (W ∪ X)) := by exact (Parley.Items.Stdlib.Functions.mun_image_monotone (X := A) (Y := X) (Z := W ∪ X) (f := f) (W := Set.univ) s8 (by parley_set_side))
  -- 10. mun:union-subset X := f[W], Y := f[X], Z := f[W ∪ X], from 6, 9
  have s10 : f '' (A ∩ W) ∪ f '' (A ∩ X) ⊆ f '' (A ∩ (W ∪ X)) := by exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := f '' (A ∩ W)) (Y := f '' (A ∩ X)) (Z := f '' (A ∩ (W ∪ X))) s6 s9)
  -- 11. mun:subset-antisymmetric, from 3, 10
  have s11 : f '' (A ∩ (W ∪ X)) = f '' (A ∩ W) ∪ f '' (A ∩ X) := by exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := f '' (A ∩ (W ∪ X))) (Y := f '' (A ∩ W) ∪ f '' (A ∩ X)) s3 s10)
  all_goals exact s11

end Parley.Proofs.Hammack.ImageOfUnion.ImageOfUnion
