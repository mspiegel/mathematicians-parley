module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
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
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/image-empty.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ImageEmpty.ImageEmpty

theorem image_empty {α β : Type*} [Nonempty α] [Nonempty β] (A : Set α) (Y : Set β) (F : α → β) (hH2 : Set.MapsTo F A Y) (B : Set α) (hH3 : B ⊆ A) :
    (F '' (A ∩ B) = ∅ ↔ B = ∅) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. proof
    have s1 : ∀ t ∈ B, t ∈ (∅ : Set α) := by
      intro t hK1
      -- 1.1. mun:value-in-image, from H3, K1
      have s1_1 : F t ∈ F '' (A ∩ B) := by exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := B) (f := F) (s := t) (W := Y) hH3 hK1 hH2)
      -- 1.2. substitute F[B] = ∅ (D1) into line 1.1
      have s1_2 : F t ∈ (∅ : Set β) := Eq.subst (motive := (fun u : Set β => F t ∈ u)) hD1 s1_1
      -- 1.3. inspection
      have s1_3 : ¬ F t ∈ (∅ : Set β) := Set.notMem_empty _
      exact absurd s1_2 s1_3
    -- 2. def:subset, from 1
    have s2 : B ⊆ ∅ := ((Parley.Items.Stdlib.Sets.def_subset (X := B) (Y := ∅))).mpr s1
    -- 3. mun:subset-empty, from 2
    exact ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := B))).mp s2
  · skip
    intro hD2
    -- 4. proof
    have s4 : ∀ u ∈ F '' (A ∩ B), u ∈ (∅ : Set β) := by
      intro u hK2
      -- 4.1. def:image, from H3, K2
      have s4_1 : ∃ s ∈ B, u = F s := by exact ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := B) (f := F) (u := u) (W := Y) hH3 hH2)).mp hK2
      -- 4.2. obtain s from line 4.1
      obtain ⟨s, s4_2a, s4_2b⟩ := s4_1
      -- 4.3. substitute B = ∅ (D2) into line 4.2
      have s4_3 : s ∈ (∅ : Set α) := Eq.subst (motive := (fun t : Set α => s ∈ t)) hD2 s4_2a
      -- 4.4. inspection
      have s4_4 : ¬ s ∈ (∅ : Set α) := Set.notMem_empty _
      exact absurd s4_3 s4_4
    -- 5. def:subset, from 4
    have s5 : F '' (A ∩ B) ⊆ ∅ := ((Parley.Items.Stdlib.Sets.def_subset (X := F '' (A ∩ B)) (Y := ∅))).mpr s4
    -- 6. mun:subset-empty, from 5
    exact ((Parley.Items.Stdlib.Sets.mun_subset_empty (Y := F '' (A ∩ B)))).mp s5

end Parley.Proofs.Setmm.ImageEmpty.ImageEmpty
