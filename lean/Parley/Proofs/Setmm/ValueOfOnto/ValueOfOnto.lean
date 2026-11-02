module

public import Tactics
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/value-of-onto.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ValueOfOnto.ValueOfOnto

theorem value_of_onto {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B) (hH4 : F '' A = B) (y : α) (hH5 : y ∈ B) :
    (∃ x ∈ A, y = F x) := by
  -- 1. substitute F[A] = B (H4) into H5
  have s1 : y ∈ F '' A := by parley_subst_at hH4 hH5
  -- 2. obtain x: def:image u := y, Y := A, from 1
  have r16_1 : A ⊆ A := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := A)) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := A))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := A)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := A)) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := A)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := A)); parley_side)
  obtain ⟨x, s2a, s2b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := A) (f := F) (u := y) (W := Set.univ) (by parley_side) (by parley_side))).mp (by parley_side)
  -- 3. exhibit, from 2
  have s3 : ∃ x ∈ A, y = F x := ⟨x, by parley_side, by parley_side⟩
  all_goals parley_side

end Parley.Proofs.Setmm.ValueOfOnto.ValueOfOnto
