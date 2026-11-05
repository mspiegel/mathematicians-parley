module

public import SetTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/subsets.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Subsets.AddElementBijection

theorem add_element_bijection {α : Type*} (X : Set α) (a : α) (hH2 : ¬ a ∈ X) :
    (∃ g : Set α → Set α, Set.BijOn g (𝒫 X) ((fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 X))) := by
  -- 1. proof
  have s1 : ∀ S ∈ 𝒫 X, ∀ T ∈ 𝒫 X, S ∪ ({a} : Set α) = T ∪ ({a} : Set α) → S = T := by
    intro S hK1
    intro T hK2
    intro hK3
    -- 1.1. def:powerset, from K1
    have s1_1 : S ⊆ X := by first | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := S))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := S))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := S))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := S))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := S))).mp (by parley_set_side); parley_set_side)
    -- 1.2. def:powerset S := T, from K2
    have s1_2 : T ⊆ X := by first | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := T))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := T))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := T))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := T))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := T))).mp (by parley_set_side); parley_set_side)
    -- 1.3. mun:not-in-subset Y := S, Z := X, from H2, 1.1
    have s1_3 : ¬ a ∈ S := by first | exact (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := S) (Z := X) (a := a) hH2 s1_1) | exact ((Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := S) (Z := X) (a := a) hH2 s1_1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := S) (Z := X) (a := a) hH2 s1_1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := S) (Z := X) (a := a) hH2 s1_1) | (have h := (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := S) (Z := X) (a := a) hH2 s1_1); parley_set_side)
    -- 1.4. mun:not-in-subset Y := T, Z := X, from H2, 1.2
    have s1_4 : ¬ a ∈ T := by first | exact (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T) (Z := X) (a := a) hH2 s1_2) | exact ((Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T) (Z := X) (a := a) hH2 s1_2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T) (Z := X) (a := a) hH2 s1_2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T) (Z := X) (a := a) hH2 s1_2) | (have h := (Parley.Items.Stdlib.Sets.mun_not_in_subset (Y := T) (Z := X) (a := a) hH2 s1_2); parley_set_side)
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
  -- 2. mun:image-of-injection Y := 𝒫X, from 1
  have s2 : ∃ g : Set α → Set α, Set.BijOn g (𝒫 X) ((fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 X)) := by first | exact (Parley.Items.Stdlib.Functions.mun_image_of_injection (Y := 𝒫 X) (a := a) s1) | exact ((Parley.Items.Stdlib.Functions.mun_image_of_injection (Y := 𝒫 X) (a := a) s1)).symm | simpa using (Parley.Items.Stdlib.Functions.mun_image_of_injection (Y := 𝒫 X) (a := a) s1) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_image_of_injection (Y := 𝒫 X) (a := a) s1) | (have h := (Parley.Items.Stdlib.Functions.mun_image_of_injection (Y := 𝒫 X) (a := a) s1); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Wiedijk.Subsets.AddElementBijection
