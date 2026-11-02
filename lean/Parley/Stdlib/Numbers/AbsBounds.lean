module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from corpus/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Numbers.AbsBounds

theorem abs_bounds (x : ℝ) :
    x ≤ abs x ∧ -x ≤ abs x := by
  -- 1. mun:nonneg-or-neg
  have s1 : x ≥ 0 ∨ x < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := x)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := x))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := x)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := x)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := x)); parley_side)
  -- 2. cases, from 1
  have s2a_all : x ≤ abs x ∧ -x ≤ abs x := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. def:abs, from C1
      have s2_1 : abs x = x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := x)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := x)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := x)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := x)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := x)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := x)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := x)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := x)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := x)) (by parley_side); parley_side)
      -- 2.2. inequalities
      have s2_2 : x ≤ abs x := by parley_side
      -- 2.3. inequalities
      have s2_3 : -x ≤ 0 := by parley_side
      -- 2.4. transitivity, from 2.3, C1, 2.1
      have s2_4 : -x ≤ abs x := by parley_side
      -- 2.5. join 2.2, 2.4
      have s2_5a : x ≤ abs x := by parley_side
      have s2_5b : -x ≤ abs x := by parley_side
      all_goals parley_side
    · skip
      -- 2.6. def:abs, from C2
      have s2_6 : abs x = -x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_2 (x := x)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := x)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := x)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_2 (x := x)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_2 (x := x)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := x)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := x)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := x)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := x)) (by parley_side); parley_side)
      -- 2.7. inequalities
      have s2_7 : -x ≤ abs x := by parley_side
      -- 2.8. inequalities
      have s2_8 : 0 < -x := by parley_side
      -- 2.9. transitivity, from C2, 2.8, 2.6
      have s2_9 : x < abs x := by parley_side
      -- 2.10. inequalities
      have s2_10 : x ≤ abs x := by parley_side
      -- 2.11. join 2.7, 2.10
      have s2_11a : x ≤ abs x := by parley_side
      have s2_11b : -x ≤ abs x := by parley_side
      all_goals parley_side
  obtain ⟨s2a, s2b⟩ := s2a_all
  exact ⟨by parley_side, by parley_side⟩

end Parley.Stdlib.Numbers.AbsBounds
