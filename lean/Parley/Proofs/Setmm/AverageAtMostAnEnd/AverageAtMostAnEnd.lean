module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning

/-! Written from proofs/setmm/average-at-most-an-end.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.AverageAtMostAnEnd.AverageAtMostAnEnd

theorem average_at_most_an_end (A : ℝ) (B : ℝ) :
    ((A + B) / 2 ≤ A ∨ (A + B) / 2 ≤ B) := by
  -- 1. mun:nonneg-or-neg x := B − A
  have s1 : B - A ≥ 0 ∨ B - A < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := B - A)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := B - A))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := B - A)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := B - A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := B - A)); parley_side)
  -- 2. cases, from 1
  have s2 : (A + B) / 2 ≤ A ∨ (A + B) / 2 ≤ B := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. inequalities
      have s2_1 : (A + B) / 2 ≤ B := by parley_order
      -- 2.2. mun:or-right, from 2.1
      have s2_2 : (A + B) / 2 ≤ A ∨ (A + B) / 2 ≤ B := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (A + B) / 2 ≤ A) (Q := (A + B) / 2 ≤ B) s2_1) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := (A + B) / 2 ≤ A) (Q := (A + B) / 2 ≤ B) s2_1)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (A + B) / 2 ≤ A) (Q := (A + B) / 2 ≤ B) s2_1) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (A + B) / 2 ≤ A) (Q := (A + B) / 2 ≤ B) s2_1) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := (A + B) / 2 ≤ A) (Q := (A + B) / 2 ≤ B) s2_1); parley_side)
      all_goals parley_side
    · skip
      -- 2.3. inequalities
      have s2_3 : (A + B) / 2 ≤ A := by parley_order
      -- 2.4. mun:or-left, from 2.3
      have s2_4 : (A + B) / 2 ≤ A ∨ (A + B) / 2 ≤ B := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (A + B) / 2 ≤ A) (Q := (A + B) / 2 ≤ B) s2_3) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := (A + B) / 2 ≤ A) (Q := (A + B) / 2 ≤ B) s2_3)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (A + B) / 2 ≤ A) (Q := (A + B) / 2 ≤ B) s2_3) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (A + B) / 2 ≤ A) (Q := (A + B) / 2 ≤ B) s2_3) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := (A + B) / 2 ≤ A) (Q := (A + B) / 2 ≤ B) s2_3); parley_side)
      all_goals parley_side
  all_goals exact s2

end Parley.Proofs.Setmm.AverageAtMostAnEnd.AverageAtMostAnEnd
