module

public import PowerTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/or-over-and.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OrOverAnd.OrOverAnd

set_option maxHeartbeats 400000 in
theorem or_over_and (a : ℝ) (b : ℝ) (c : ℝ) :
    (a = 0 ∨ b = 0 ∧ c = 0 ↔ (a = 0 ∨ b = 0) ∧ (a = 0 ∨ c = 0)) := by
  -- the theorem. both directions
  have sThm : a = 0 ∨ b = 0 ∧ c = 0 ↔ (a = 0 ∨ b = 0) ∧ (a = 0 ∨ c = 0) := by
    constructor
    · skip
      intro hD1
      -- 1. cases, from D1
      have s1 : (a = 0 ∨ b = 0) ∧ (a = 0 ∨ c = 0) := by
        rcases hD1 with hC1 | hC2
        · skip
          -- 1.1. mun:or-left, from C1
          have s1_1 : a = 0 ∨ b = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0) hC1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0) hC1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0) hC1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0) hC1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0) hC1); parley_side)
          -- 1.2. mun:or-left, from C1
          have s1_2 : a = 0 ∨ c = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := c = 0) hC1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := c = 0) hC1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := c = 0) hC1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := c = 0) hC1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := c = 0) hC1); parley_side)
          -- 1.3. join 1.1, 1.2
          have s1_3 : (a = 0 ∨ b = 0) ∧ (a = 0 ∨ c = 0) := by parley_side
          all_goals parley_side
        · skip
          -- 1.4. mun:or-right, from C2
          have s1_4 : a = 0 ∨ b = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0) hC2.1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0) hC2.1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0) hC2.1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0) hC2.1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0) hC2.1); parley_side)
          -- 1.5. mun:or-right, from C2
          have s1_5 : a = 0 ∨ c = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := c = 0) hC2.2) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := c = 0) hC2.2)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := c = 0) hC2.2) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := c = 0) hC2.2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := c = 0) hC2.2); parley_side)
          -- 1.6. join 1.4, 1.5
          have s1_6 : (a = 0 ∨ b = 0) ∧ (a = 0 ∨ c = 0) := by parley_side
          all_goals parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 2. restate D2
      have s2 : a = 0 ∨ b = 0 := by parley_side
      -- 3. restate D2
      have s3 : a = 0 ∨ c = 0 := by parley_side
      -- 4. axi:excluded-middle P := a = 0
      have s4 : a = 0 ∨ a ≠ 0 := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a = 0)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a = 0))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a = 0)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a = 0)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a = 0)); parley_side)
      -- 5. cases, from 4
      have s5 : a = 0 ∨ b = 0 ∧ c = 0 := by
        rcases s4 with hC3 | hC4
        · skip
          -- 5.1. mun:or-left, from C3
          have s5_1 : a = 0 ∨ b = 0 ∧ c = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0 ∧ c = 0) hC3) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0 ∧ c = 0) hC3)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0 ∧ c = 0) hC3) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0 ∧ c = 0) hC3) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0 ∧ c = 0) hC3); parley_side)
          all_goals parley_side
        · skip
          -- 5.2. mun:disjunctive-syllogism-left, from C4, 2
          have s5_2 : b = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := b = 0) s2 hC4) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := b = 0) s2 hC4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := b = 0) s2 hC4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := b = 0) s2 hC4) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := b = 0) s2 hC4)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := b = 0) s2 hC4); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := b = 0) s2 hC4); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := b = 0) s2 hC4); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := b = 0) s2 hC4); parley_side)
          -- 5.3. mun:disjunctive-syllogism-left, from C4, 3
          have s5_3 : c = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := c = 0) s3 hC4) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := c = 0) s3 hC4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := c = 0) s3 hC4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := c = 0) s3 hC4) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := c = 0) s3 hC4)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := c = 0) s3 hC4); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := c = 0) s3 hC4); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := c = 0) s3 hC4); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := a = 0) (Q := c = 0) s3 hC4); parley_side)
          -- 5.4. join 5.2, 5.3
          have s5_4 : b = 0 ∧ c = 0 := by parley_side
          -- 5.5. mun:or-right, from 5.4
          have s5_5 : a = 0 ∨ b = 0 ∧ c = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0 ∧ c = 0) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0 ∧ c = 0) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0 ∧ c = 0) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0 ∧ c = 0) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0 ∧ c = 0) (by parley_side)); parley_side)
          all_goals parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.OrOverAnd.OrOverAnd
