module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/image-of-part.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ImageOfPart.ImageOfPart

theorem image_of_part {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B) (X : Set α) (hH4 : X ⊆ A) :
    F '' (A ∩ X) ⊆ F '' (A ∩ A) := by
  -- 1. proof
  have s1 : ∀ u ∈ F '' (A ∩ X), u ∈ F '' (A ∩ A) := by
    intro u hK1
    -- 1.1. obtain s: def:image Y := X, from H4, K1
    obtain ⟨s, s1_1a, s1_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := X) (f := F) (u := u) (W := Set.univ) hH4 (by parley_set_side))).mp hK1
    -- 1.2. mun:in-subset, from H4, 1.1
    have s1_2 : s ∈ A := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := s) hH4 s1_1a)
    -- 1.3. mun:value-in-image Y := A, from 1.2
    have r25_1 : A ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := A))
    have s1_3 : F s ∈ F '' (A ∩ A) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A) (f := F) (s := s) (W := Set.univ) r25_1 s1_2 (by parley_set_side))
    -- 1.4. substitute u = F(s) (line 1.1) into line 1.3
    parley_subst_at s1_1b s1_3
  -- 2. def:subset, from 1
  exact ((Parley.Items.Stdlib.Sets.def_subset (X := F '' (A ∩ X)) (Y := F '' (A ∩ A)))).mpr s1

end Parley.Proofs.Setmm.ImageOfPart.ImageOfPart
