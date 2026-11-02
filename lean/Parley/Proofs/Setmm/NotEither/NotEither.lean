module

public import LeanBridges
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/not-either.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.NotEither.NotEither

theorem not_either (a : ℝ) (b : ℝ) :
    (¬ (a = 0 ∨ b = 0) ↔ a ≠ 0 ∧ b ≠ 0) := by
  -- the theorem. both directions
  have sThm : ¬ (a = 0 ∨ b = 0) ↔ a ≠ 0 ∧ b ≠ 0 := by
    constructor
    · skip
      intro hD1
      -- 1. contradiction
      have s1 : a ≠ 0 := by
        by_contra hc_hS1
        have hS1 : a = 0 := by parley_suppose hc_hS1
        -- 1.1. mun:or-left, from S1
        have s1_1 : a = 0 ∨ b = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := a = 0) (Q := b = 0) (by parley_side)); parley_side)
        -- 1.2. restate D1
        have s1_2 : ¬ (a = 0 ∨ b = 0) := by parley_side
        all_goals parley_side
      -- 2. contradiction
      have s2 : b ≠ 0 := by
        by_contra hc_hS2
        have hS2 : b = 0 := by parley_suppose hc_hS2
        -- 2.1. mun:or-right, from S2
        have s2_1 : a = 0 ∨ b = 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := a = 0) (Q := b = 0) (by parley_side)); parley_side)
        -- 2.2. restate D1
        have s2_2 : ¬ (a = 0 ∨ b = 0) := by parley_side
        all_goals parley_side
      -- 3. join 1, 2
      have s3 : a ≠ 0 ∧ b ≠ 0 := by parley_side
      all_goals parley_side
    · skip
      intro hD2
      by_contra hc_hS3
      have hS3 : a = 0 ∨ b = 0 := by parley_suppose hc_hS3
      -- 4. mun:disjunctive-syllogism, from D2, S3
      have s4 : a = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := a = 0) (Q := b = 0) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := a = 0) (Q := b = 0) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := a = 0) (Q := b = 0) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := a = 0) (Q := b = 0) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := a = 0) (Q := b = 0) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := a = 0) (Q := b = 0) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := a = 0) (Q := b = 0) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := a = 0) (Q := b = 0) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := a = 0) (Q := b = 0) (by parley_side) (by parley_side)); parley_side)
      -- 5. restate D2
      have s5 : a ≠ 0 := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.NotEither.NotEither
