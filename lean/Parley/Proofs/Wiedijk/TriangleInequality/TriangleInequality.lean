module

public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds

/-! Written from proofs/wiedijk/triangle-inequality.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.TriangleInequality.TriangleInequality

theorem triangle_inequality (a : ℝ) (b : ℝ) :
    abs (a + b) ≤ abs a + abs b := by
  -- 1. mun:nonneg-or-neg x := a + b
  have s1 : a + b ≥ 0 ∨ a + b < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a + b)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a + b))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a + b)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a + b)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a + b)); parley_side)
  -- 2. thm:abs-bounds x := a
  have s2a : a ≤ abs a := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).1] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).1 | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).1; parley_side)
  have s2b : -a ≤ abs a := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).2] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).2; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).2 | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := a)).2; parley_side)
  -- 3. thm:abs-bounds x := b
  have s3a : b ≤ abs b := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).1] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).1 | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).1; parley_side)
  have s3b : -b ≤ abs b := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).2] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).2; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).2 | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := b)).2; parley_side)
  -- 4. cases, from 1
  have s4 : abs (a + b) ≤ abs a + abs b := by
    rcases s1 with hC1 | hC2
    · skip
      -- 4.1. inequalities, from 2, 3
      have s4_1 : a + b ≤ abs a + abs b := by parley_order
      -- 4.2. calculation
      have s4_2 : abs (a + b) ≤ abs a + abs b := by
        calc abs (a + b) = a + b := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := a + b)) (by parley_side); parley_side)
          _ ≤ abs a + abs b := by parley_side
      all_goals parley_side
    · skip
      -- 4.3. inequalities, from 2, 3
      have s4_3 : -a + -b ≤ abs a + abs b := by parley_order
      -- 4.4. calculation
      have s4_4 : abs (a + b) ≤ abs a + abs b := by
        calc abs (a + b) = -(a + b) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_2 (x := a + b)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := a + b)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := a + b)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_2 (x := a + b)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_2 (x := a + b)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := a + b)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := a + b)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := a + b)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := a + b)) (by parley_side); parley_side)
          _ = -a + -b := by parley_ring
          _ ≤ abs a + abs b := by parley_side
      all_goals parley_side
  all_goals exact s4

end Parley.Proofs.Wiedijk.TriangleInequality.TriangleInequality
