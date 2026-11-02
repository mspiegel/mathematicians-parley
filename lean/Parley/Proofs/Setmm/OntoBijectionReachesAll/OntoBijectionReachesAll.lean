module

public import Tactics
public import Parley.Proofs.Setmm.ValueOfOnto.ValueOfOnto

/-! Written from proofs/setmm/onto-bijection-reaches-all.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OntoBijectionReachesAll.OntoBijectionReachesAll

theorem onto_bijection_reaches_all {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (hH4 : F '' A = B) :
    (∀ y ∈ B, ∃ x ∈ A, y = F x) := by
  -- 1. proof
  have s1 : ∀ y ∈ B, ∃ x ∈ A, y = F x := by
    intro y hK1
    -- 1.1. thm:value-of-onto, from H4, K1
    have s1_1 : ∃ x ∈ A, y = F x := by first | exact (Parley.Proofs.Setmm.ValueOfOnto.ValueOfOnto.value_of_onto (A := A) (B := B) (F := F) (by parley_side) (by parley_side) (y := y) (by parley_side)) | exact ((Parley.Proofs.Setmm.ValueOfOnto.ValueOfOnto.value_of_onto (A := A) (B := B) (F := F) (by parley_side) (by parley_side) (y := y) (by parley_side))).symm | simpa using (Parley.Proofs.Setmm.ValueOfOnto.ValueOfOnto.value_of_onto (A := A) (B := B) (F := F) (by parley_side) (by parley_side) (y := y) (by parley_side)) | exact_mod_cast (Parley.Proofs.Setmm.ValueOfOnto.ValueOfOnto.value_of_onto (A := A) (B := B) (F := F) (by parley_side) (by parley_side) (y := y) (by parley_side)) | (have h := (Parley.Proofs.Setmm.ValueOfOnto.ValueOfOnto.value_of_onto (A := A) (B := B) (F := F) (by parley_side) (by parley_side) (y := y) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Proofs.Setmm.ValueOfOnto.ValueOfOnto.value_of_onto (A := A) (B := B) (F := F) (by parley_side) (by parley_side) (y := y) (by parley_side)); parley_side)
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.OntoBijectionReachesAll.OntoBijectionReachesAll
