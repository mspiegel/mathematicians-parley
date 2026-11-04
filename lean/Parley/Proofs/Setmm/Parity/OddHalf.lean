module

public import AlgebraTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from proofs/setmm/parity.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.Parity.OddHalf

theorem odd_half (N : ℤ) :
    (Odd N ↔ (∃ m : ℤ, (m : ℚ) = ((N : ℚ) - 1) / 2)) := by
  -- the theorem. both directions
  have sThm : Odd N ↔ (∃ m : ℤ, (m : ℚ) = ((N : ℚ) - 1) / 2) := by
    constructor
    · skip
      intro hD1
      -- 1. obtain k: def:odd n := N, from D1
      obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mp (by parley_side)
      -- 2. algebra, from 1
      have s2 : ((N : ℚ) - 1) / 2 = (k : ℚ) := by
        have s1_w : (N : ℚ) = 2 * (k : ℚ) + 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1; push_cast at h; linear_combination (norm := parley_norm) h
        linear_combination (norm := parley_norm) ((1) / ((2))) * s1_w
      -- 3. membership, from 2
      have s3 : ∃ m : ℤ, (m : ℚ) = ((N : ℚ) - 1) / 2 := ⟨k, by first | (push_cast; linarith [s2]) | (rw [s2]; push_cast; ring) | (rw [← s2]; push_cast; ring) | exact s2 | exact s2.symm⟩
      all_goals parley_side
    · skip
      intro hD2
      -- 4. algebra
      have s4 : (N : ℚ) = 2 * (((N : ℚ) - 1) / 2) + 1 := by parley_ring
      -- 5. def:odd n := N, from D2, 4
      have s5 : Odd N := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mpr ⟨Classical.choose hD2, by have := Classical.choose_spec hD2; parley_side⟩ | (have h := ((Parley.Items.Stdlib.Divisibility.def_odd (n := N))).mpr ⟨Classical.choose hD2, by have := Classical.choose_spec hD2; parley_side⟩; parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.Parity.OddHalf
