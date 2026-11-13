module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/preimage-of-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PreimageOfUnion.PreimageOfUnion

theorem preimage_of_union {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B) (Y : Set α) (hH4 : Y ⊆ B) (Z : Set α) (hH5 : Z ⊆ B) :
    A ∩ f ⁻¹' (Y ∪ Z) = A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∩ f ⁻¹' (Y ∪ Z), u ∈ A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z := by
    intro u hK1
    -- 1.1. def:preimage Z := Y ∪ Z, from K1
    have s1_1a : u ∈ A := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (Set.mapsTo_univ _ _))).mp hK1).1
    have s1_1b : f u ∈ Y ∪ Z := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (Set.mapsTo_univ _ _))).mp hK1).2
    -- 1.2. def:union u := f(u), from 1.1
    have s1_2 : f u ∈ Y ∨ f u ∈ Z := by exact ((Parley.Items.Stdlib.Sets.def_union (Y := Y) (Z := Z) (u := f u))).mp s1_1b
    -- 1.3. cases, from 1.2
    rcases s1_2 with hC1 | hC2
    · skip
      -- 1.3.1. def:preimage Z := Y, from C1, 1.1
      have s1_3_1 : u ∈ A ∩ f ⁻¹' Y := ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (Set.mapsTo_univ _ _))).mpr ⟨s1_1a, hC1⟩
      -- 1.3.2. mun:in-union-left Y := f⁻¹[Y], Z := f⁻¹[Z], from 1.3.1
      exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u) s1_3_1)
    · skip
      -- 1.3.3. def:preimage, from C2, 1.1
      have s1_3_3 : u ∈ A ∩ f ⁻¹' Z := ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (Set.mapsTo_univ _ _))).mpr ⟨s1_1a, hC2⟩
      -- 1.3.4. mun:in-union-right Y := f⁻¹[Y], Z := f⁻¹[Z], from 1.3.3
      exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u) s1_3_3)
  -- 2. def:subset, from 1
  have s2 : A ∩ f ⁻¹' (Y ∪ Z) ⊆ A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' (Y ∪ Z)) (Y := A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z))).mpr s1
  -- 3. proof
  have s3 : ∀ u ∈ A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z, u ∈ A ∩ f ⁻¹' (Y ∪ Z) := by
    intro u hK2
    -- 3.1. def:union Y := f⁻¹[Y], Z := f⁻¹[Z], from K2
    have s3_1 : u ∈ A ∩ f ⁻¹' Y ∨ u ∈ A ∩ f ⁻¹' Z := by exact ((Parley.Items.Stdlib.Sets.def_union (Y := A ∩ f ⁻¹' Y) (Z := A ∩ f ⁻¹' Z) (u := u))).mp hK2
    -- 3.2. cases, from 3.1
    rcases s3_1 with hC3 | hC4
    · skip
      -- 3.2.1. def:preimage Z := Y, from C3
      have s3_2_1a : u ∈ A := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (Set.mapsTo_univ _ _))).mp hC3).1
      have s3_2_1b : f u ∈ Y := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y) (f := f) (u := u) (W := Set.univ) (Set.mapsTo_univ _ _))).mp hC3).2
      -- 3.2.2. mun:in-union-left u := f(u), from 3.2.1
      have s3_2_2 : f u ∈ Y ∪ Z := by exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := Y) (Z := Z) (u := f u) s3_2_1b)
      -- 3.2.3. def:preimage Z := Y ∪ Z, from 3.2.1, 3.2.2
      exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (Set.mapsTo_univ _ _))).mpr ⟨s3_2_1a, s3_2_2⟩
    · skip
      -- 3.2.4. def:preimage, from C4
      have s3_2_4a : u ∈ A := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (Set.mapsTo_univ _ _))).mp hC4).1
      have s3_2_4b : f u ∈ Z := by exact (((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Z) (f := f) (u := u) (W := Set.univ) (Set.mapsTo_univ _ _))).mp hC4).2
      -- 3.2.5. mun:in-union-right u := f(u), from 3.2.4
      have s3_2_5 : f u ∈ Y ∪ Z := by exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := Y) (Z := Z) (u := f u) s3_2_4b)
      -- 3.2.6. def:preimage Z := Y ∪ Z, from 3.2.4, 3.2.5
      exact ((Parley.Items.Stdlib.Functions.def_preimage (X := A) (Z := Y ∪ Z) (f := f) (u := u) (W := Set.univ) (Set.mapsTo_univ _ _))).mpr ⟨s3_2_4a, s3_2_5⟩
  -- 4. def:subset, from 3
  have s4 : A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z ⊆ A ∩ f ⁻¹' (Y ∪ Z) := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z) (Y := A ∩ f ⁻¹' (Y ∪ Z)))).mpr s3
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ f ⁻¹' (Y ∪ Z)) (Y := A ∩ f ⁻¹' Y ∪ A ∩ f ⁻¹' Z) s2 s4)

end Parley.Proofs.Hammack.PreimageOfUnion.PreimageOfUnion
