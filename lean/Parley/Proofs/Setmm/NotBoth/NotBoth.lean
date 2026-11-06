module

public import ArithTactics
public import PowerTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/not-both.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.NotBoth.NotBoth

theorem not_both (a : ℝ) (b : ℝ) :
    (¬ (a = 0 ∧ b = 0) ↔ a ≠ 0 ∨ b ≠ 0) := by
  -- the theorem. both directions
  have sThm : ¬ (a = 0 ∧ b = 0) ↔ a ≠ 0 ∨ b ≠ 0 := by
    constructor
    · skip
      intro hD1
      by_contra hc_hS
      have hS : ¬ (a ≠ 0 ∨ b ≠ 0) := by parley_suppose hc_hS
      -- 1. mun:not-either, from S
      have s1a : ¬ a ≠ 0 := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := a ≠ 0) (Q := b ≠ 0))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := a ≠ 0) (Q := b ≠ 0))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := a ≠ 0) (Q := b ≠ 0))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := a ≠ 0) (Q := b ≠ 0))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := a ≠ 0) (Q := b ≠ 0))).mp (by parley_side)).1; parley_side)
      have s1b : ¬ b ≠ 0 := by first | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := a ≠ 0) (Q := b ≠ 0))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Reasoning.mun_not_either (P := a ≠ 0) (Q := b ≠ 0))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := a ≠ 0) (Q := b ≠ 0))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := a ≠ 0) (Q := b ≠ 0))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := a ≠ 0) (Q := b ≠ 0))).mp (by parley_side)).2; parley_side)
      -- 2. mun:double-negation, from 1
      have s2 : a = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := a = 0) s1a) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := a = 0) s1a); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := a = 0) s1a); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := a = 0) s1a) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_double_negation (P := a = 0) s1a)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := a = 0) s1a); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := a = 0) s1a); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := a = 0) s1a); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := a = 0) s1a); parley_side)
      -- 3. mun:double-negation, from 1
      have s3 : b = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := b = 0) s1b) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := b = 0) s1b); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := b = 0) s1b); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := b = 0) s1b) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_double_negation (P := b = 0) s1b)).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := b = 0) s1b); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := b = 0) s1b); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := b = 0) s1b); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := b = 0) s1b); parley_side)
      -- 4. join 2, 3
      have s4 : a = 0 ∧ b = 0 := by parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 5. cases, from D2
      have s5 : ¬ (a = 0 ∧ b = 0) := by
        rcases hD2 with hC1 | hC2
        · skip
          -- 5.1. restate C1
          have s5_1 : a ≠ 0 := by parley_side
          all_goals parley_side
        · skip
          -- 5.2. restate C2
          have s5_2 : b ≠ 0 := by parley_side
          all_goals parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.NotBoth.NotBoth
