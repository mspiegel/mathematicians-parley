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

/-! Written from proofs/setmm/image-is-codomain.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ImageIsCodomain.ImageIsCodomain

theorem image_is_codomain {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B) (hH4 : ∀ y ∈ B, ∃ x ∈ A, y = F x) :
    F '' (A ∩ A) = B := by
  -- 1. mun:image-within f := F
  have s1 : F '' (A ∩ A) ⊆ B := by exact (Parley.Items.Stdlib.Functions.mun_image_within (X := A) (W := B) (Y := A) (f := F) (by parley_set_side))
  -- 2. proof
  have s2 : ∀ y ∈ B, y ∈ F '' (A ∩ A) := by
    intro y hK1
    -- 2.1. obtain x from H4
    obtain ⟨x, s2_1a, s2_1b⟩ := (hH4 y hK1)
    -- 2.2. mun:value-in-image Y := A, s := x, from 2.1
    have r25_1 : A ⊆ A := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := A))
    have s2_2 : F x ∈ F '' (A ∩ A) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A) (f := F) (s := x) (W := Set.univ) r25_1 s2_1a (by parley_set_side))
    -- 2.3. substitute y = F(x) (line 2.1) into line 2.2
    parley_subst_at s2_1b s2_2
  -- 3. def:subset, from 2
  have s3 : B ⊆ F '' (A ∩ A) := ((Parley.Items.Stdlib.Sets.def_subset (X := B) (Y := F '' (A ∩ A)))).mpr s2
  -- 4. mun:subset-antisymmetric, from 1, 3
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := F '' (A ∩ A)) (Y := B) s1 s3)

end Parley.Proofs.Setmm.ImageIsCodomain.ImageIsCodomain
