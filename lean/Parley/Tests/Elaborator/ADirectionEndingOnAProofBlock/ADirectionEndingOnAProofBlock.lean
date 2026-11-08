module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-direction-ending-on-a-proof-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADirectionEndingOnAProofBlock.ADirectionEndingOnAProofBlock

theorem a_direction_ending_on_a_proof_block {α : Type*} (A : Set α) (B : Set α) :
    (A ⊆ B ↔ (∀ t ∈ A, t ∈ B)) := by
  -- 1. both directions
  constructor
  · skip
    intro hD1
    -- 1.1. proof
    intro t hK1
    -- 1.1.1. mun:in-subset X := A, Y := B, u := t, from D1, K1
    exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 hK1)
  · skip
    intro hD2
    -- 1.2. def:subset, from D2
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr hD2 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr hD2; parley_set_side)

end Parley.Tests.Elaborator.ADirectionEndingOnAProofBlock.ADirectionEndingOnAProofBlock
