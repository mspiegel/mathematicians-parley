module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-direction-ending-on-a-proof-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADirectionEndingOnAProofBlock.ADirectionEndingOnAProofBlock

theorem a_direction_ending_on_a_proof_block {α : Type*} (A : Set α) (B : Set α) :
    (A ⊆ B ↔ (∀ t ∈ A, t ∈ B)) := by
  -- 1. both directions
  have s1 : A ⊆ B ↔ (∀ t ∈ A, t ∈ B) := by
    constructor
    · skip
      intro hD1
      -- 1.1. proof
      have s1_1 : ∀ t ∈ A, t ∈ B := by
        intro t hK1
        -- 1.1.1. mun:in-subset X := A, Y := B, u := t, from D1, K1
        have s1_1_1 : t ∈ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) (by parley_set_side) (by parley_set_side)); parley_set_side)
        all_goals parley_set_side
      all_goals parley_set_side
    · skip
      intro hD2
      -- 1.2. def:subset, from D2
      have s1_2 : A ⊆ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr (by parley_set_side); parley_set_side)
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Tests.Elaborator.ADirectionEndingOnAProofBlock.ADirectionEndingOnAProofBlock
