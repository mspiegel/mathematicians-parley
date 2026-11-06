module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/and-over-or.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.AndOverOr.AndOverOr

set_option maxHeartbeats 400000 in
theorem and_over_or (a : ℝ) (b : ℝ) (c : ℝ) :
    (a = 0 ∧ (b = 0 ∨ c = 0) ↔ a = 0 ∧ b = 0 ∨ a = 0 ∧ c = 0) := by
  -- the theorem. both directions
  have sThm : a = 0 ∧ (b = 0 ∨ c = 0) ↔ a = 0 ∧ b = 0 ∨ a = 0 ∧ c = 0 := by
    constructor
    · skip
      intro hD1
      -- 1. restate D1
      have s1 : b = 0 ∨ c = 0 := by parley_side
      -- 2. cases, from 1
      have s2 : a = 0 ∧ b = 0 ∨ a = 0 ∧ c = 0 := by
        rcases s1 with hC1 | hC2
        · skip
          -- 2.1. join C1, D1
          have s2_1 : a = 0 ∧ b = 0 := by parley_side
          -- 2.2. mun:or-left, from 2.1
          have s2_2 : a = 0 ∧ b = 0 ∨ a = 0 ∧ c = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0 ∧ b = 0) (Q := a = 0 ∧ c = 0) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0 ∧ b = 0) (Q := a = 0 ∧ c = 0) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0 ∧ b = 0) (Q := a = 0 ∧ c = 0) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0 ∧ b = 0) (Q := a = 0 ∧ c = 0) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0 ∧ b = 0) (Q := a = 0 ∧ c = 0) (by parley_side)); parley_side)
          all_goals parley_side
        · skip
          -- 2.3. join C2, D1
          have s2_3 : a = 0 ∧ c = 0 := by parley_side
          -- 2.4. mun:or-right, from 2.3
          have s2_4 : a = 0 ∧ b = 0 ∨ a = 0 ∧ c = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0 ∧ b = 0) (Q := a = 0 ∧ c = 0) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0 ∧ b = 0) (Q := a = 0 ∧ c = 0) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0 ∧ b = 0) (Q := a = 0 ∧ c = 0) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0 ∧ b = 0) (Q := a = 0 ∧ c = 0) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0 ∧ b = 0) (Q := a = 0 ∧ c = 0) (by parley_side)); parley_side)
          all_goals parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 3. cases, from D2
      have s3 : a = 0 ∧ (b = 0 ∨ c = 0) := by
        rcases hD2 with hC3 | hC4
        · skip
          -- 3.1. mun:or-left, from C3
          have s3_1 : b = 0 ∨ c = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := b = 0) (Q := c = 0) hC3.2) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := b = 0) (Q := c = 0) hC3.2)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := b = 0) (Q := c = 0) hC3.2) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := b = 0) (Q := c = 0) hC3.2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := b = 0) (Q := c = 0) hC3.2); parley_side)
          -- 3.2. join C3, 3.1
          have s3_2 : a = 0 ∧ (b = 0 ∨ c = 0) := by parley_side
          all_goals parley_side
        · skip
          -- 3.3. mun:or-right, from C4
          have s3_3 : b = 0 ∨ c = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := c = 0) hC4.2) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := c = 0) hC4.2)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := c = 0) hC4.2) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := c = 0) hC4.2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := b = 0) (Q := c = 0) hC4.2); parley_side)
          -- 3.4. join C4, 3.3
          have s3_4 : a = 0 ∧ (b = 0 ∨ c = 0) := by parley_side
          all_goals parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.AndOverOr.AndOverOr
