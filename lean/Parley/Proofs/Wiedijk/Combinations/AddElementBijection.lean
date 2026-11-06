module

public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/combinations.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Combinations.AddElementBijection

theorem add_element_bijection {α : Type*} (Y : Set α) (a : α) (hH2 : ¬ a ∈ Y) (j : ℤ) :
    (∃ g : Set α → Set α, Set.BijOn g {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j} ((fun T : Set α => T ∪ ({a} : Set α)) '' {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j})) := by
  set F : Set (Set α) := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j} with hD1
  -- 1. proof
  have s1 : ∀ S ∈ F, ∀ T ∈ F, S ∪ ({a} : Set α) = T ∪ ({a} : Set α) → S = T := by
    intro S hK1
    intro T hK2
    intro hK3
    -- 1.1. def:part-builder u := S, X := Y, from D1, K1
    have s1_1 : S ⊆ Y := by
      try simp only [hD1] at *
      try push_cast at *
      first | exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := S))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := S))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := S))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := S))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := S))).mp (by parley_set_side)).1; parley_set_side)
    -- 1.2. def:part-builder u := T, X := Y, from D1, K2
    have s1_2 : T ⊆ Y := by
      try simp only [hD1] at *
      try push_cast at *
      first | exact (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := T))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := T))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := T))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := T))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_part_builder (P := (fun S : Set α => ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j)) (X := Y) (u := T))).mp (by parley_set_side)).1; parley_set_side)
    -- 1.3. mun:not-in-subset Y := S, Z := Y, from H2, 1.1
    have s1_3 : ¬ a ∈ S := by first | exact (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := S) (Z := Y) (a := a) hH2 s1_1) | exact ((Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := S) (Z := Y) (a := a) hH2 s1_1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := S) (Z := Y) (a := a) hH2 s1_1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := S) (Z := Y) (a := a) hH2 s1_1) | (have h := (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := S) (Z := Y) (a := a) hH2 s1_1); parley_set_side)
    -- 1.4. mun:not-in-subset Y := T, Z := Y, from H2, 1.2
    have s1_4 : ¬ a ∈ T := by first | exact (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T) (Z := Y) (a := a) hH2 s1_2) | exact ((Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T) (Z := Y) (a := a) hH2 s1_2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T) (Z := Y) (a := a) hH2 s1_2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T) (Z := Y) (a := a) hH2 s1_2) | (have h := (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T) (Z := Y) (a := a) hH2 s1_2); parley_set_side)
    -- 1.5. mun:difference-of-union
    have s1_5 : (S ∪ ({a} : Set α)) \ ({a} : Set α) = S \ ({a} : Set α) := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := S) (a := a)) | exact ((Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := S) (a := a))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := S) (a := a)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := S) (a := a)) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := S) (a := a)); parley_set_side)
    -- 1.6. substitute S ∪ {a} = T ∪ {a} (K3) into line 1.5
    have s1_6 : (T ∪ ({a} : Set α)) \ ({a} : Set α) = S \ ({a} : Set α) := by parley_subst_at hK3 s1_5
    -- 1.7. calculation
    have s1_7 : S = T := by
      calc S = S \ ({a} : Set α) := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := S) (a := a) s1_3) | exact ((Parley.Items.Stdlib.Sets.mun_difference_absent (Y := S) (a := a) s1_3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := S) (a := a) s1_3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := S) (a := a) s1_3) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := S) (a := a) s1_3); parley_set_side)
        _ = (T ∪ ({a} : Set α)) \ ({a} : Set α) := by parley_set_side
        _ = T \ ({a} : Set α) := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := T) (a := a)) | exact ((Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := T) (a := a))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := T) (a := a)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := T) (a := a)) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_of_union (Y := T) (a := a)); parley_set_side)
        _ = T := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := T) (a := a) s1_4) | exact ((Parley.Items.Stdlib.Sets.mun_difference_absent (Y := T) (a := a) s1_4)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := T) (a := a) s1_4) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := T) (a := a) s1_4) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_absent (Y := T) (a := a) s1_4); parley_set_side)
    all_goals parley_set_side
  -- 2. mun:image-of-injection, from D1, 1
  have s2 : ∃ g : Set α → Set α, Set.BijOn g {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j} ((fun T : Set α => T ∪ ({a} : Set α)) '' {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j}) := by
    try simp only [hD1] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Functions.mun_image_of_injection (Y := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j}) (a := a) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_image_of_injection (Y := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j}) (a := a) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_image_of_injection (Y := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j}) (a := a) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_image_of_injection (Y := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j}) (a := a) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_image_of_injection (Y := {S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = (m : ℕ∞) ∧ (m : ℤ) = j}) (a := a) (by parley_set_side)); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Wiedijk.Combinations.AddElementBijection
