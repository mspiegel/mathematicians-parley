module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/setmm/member-of-image.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MemberOfImage.MemberOfImage

theorem member_of_image {α : Type*} (A : Set α) (B : Set α) (y : α) (F : α → α) (hH3 : Set.MapsTo F A B) (X : Set α) (hH4 : X ⊆ A) :
    (y ∈ F '' (A ∩ X) ↔ (∃ x ∈ X, F x = y)) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. obtain x: def:image u := y, from D1, H4
    obtain ⟨x, s1a, s1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := X) (f := F) (u := y) (W := Set.univ) hH4 (Set.mapsTo_univ _ _))).mp hD1
    -- 2. exhibit, from 1
    exact ⟨x, s1a, s1b.symm⟩
  · skip
    intro hD2
    -- 3. obtain x from D2
    obtain ⟨x, s3a, s3b⟩ := hD2
    -- 4. mun:value-in-image Y := X, s := x, from H4, 3
    have s4 : F x ∈ F '' (A ∩ X) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := F) (s := x) (W := B) hH4 s3a hH3)
    -- 5. substitute F(x) = y (line 3) into line 4
    exact Eq.subst (motive := (fun t : α => t ∈ F '' (A ∩ X))) s3b s4

end Parley.Proofs.Setmm.MemberOfImage.MemberOfImage
