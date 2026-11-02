module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds

/-! Written from proofs/setmm/bounded-by-square.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BoundedBySquare.BoundedBySquare

theorem bounded_by_square (A : ℝ) (B : ℝ) (hH3 : 0 ≤ B) :
    (A ≤ B ∧ -A ≤ B ↔ A ^ 2 ≤ B ^ 2) := by
  -- 1. thm:abs-bounds x := A
  have s1a : A ≤ abs A := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).1] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).1 | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).1; parley_side)
  have s1b : -A ≤ abs A := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).2] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).2; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).2 | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).2; parley_side)
  -- 2. mun:abs-square x := A
  have s2 : abs A ^ 2 = A ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_square (x := A))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A)); parley_side)
  -- 3. inequalities, from 1
  have s3 : 0 ≤ 2 * abs A := by parley_side
  -- 4. inequalities
  have s4 : 0 ≤ abs A := by parley_side
  -- 5. mun:nonneg-or-neg x := A
  have s5 : A ≥ 0 ∨ A < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := A)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := A))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := A)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := A)); parley_side)
  -- 6. both directions
  have s6 : A ≤ B ∧ -A ≤ B ↔ A ^ 2 ≤ B ^ 2 := by
    constructor
    · skip
      intro hD1
      -- 6.1. cases, from 5
      have s6_1 : abs A ≤ B := by
        rcases s5 with hC1 | hC2
        · skip
          -- 6.1.1. def:abs x := A, from C1
          have s6_1_1 : abs A = A := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) (by parley_side); parley_side)
          -- 6.1.2. transitivity, from 6.1.1, D1
          have s6_1_2 : abs A ≤ B := by parley_side
          all_goals parley_side
        · skip
          -- 6.1.3. def:abs x := A, from C2
          have s6_1_3 : abs A = -A := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) (by parley_side); parley_side)
          -- 6.1.4. transitivity, from 6.1.3, D1
          have s6_1_4 : abs A ≤ B := by parley_side
          all_goals parley_side
      -- 6.2. contradiction
      have s6_2 : A ^ 2 ≤ B ^ 2 := by
        by_contra hc_hS1
        have hS1 : ¬ A ^ 2 ≤ B ^ 2 := by parley_suppose hc_hS1
        -- 6.2.1. inequalities, from S1
        have s6_2_1 : B ^ 2 < A ^ 2 := by parley_side
        -- 6.2.2. substitute |A|² = A² (line 2) into line 6.2.1
        have s6_2_2 : B ^ 2 < abs A ^ 2 := by parley_subst_at s2 s6_2_1
        -- 6.2.3. mun:square-less x := B, y := |A|, from 6.2.2
        have r70_1 : abs A ≥ 0 := by parley_side
        have r70_2 : B ≥ 0 := by parley_side
        have s6_2_3 : B < abs A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := B) (y := abs A) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := B) (y := abs A) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
        -- 6.2.4. inequalities, from 6.2.3
        have s6_2_4 : ¬ abs A ≤ B := by parley_side
        all_goals parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 6.3. contradiction
      have s6_3 : abs A ≤ B := by
        by_contra hc_hS2
        have hS2 : ¬ abs A ≤ B := by parley_suppose hc_hS2
        -- 6.3.1. inequalities, from S2
        have s6_3_1 : B < abs A := by parley_side
        -- 6.3.2. mun:square-less x := B, y := |A|, from 6.3.1
        have r88_1 : abs A ≥ 0 := by parley_side
        have r88_2 : B ≥ 0 := by parley_side
        have s6_3_2 : B ^ 2 < abs A ^ 2 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_square_less (x := B) (y := abs A) (by parley_side) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := B) (y := abs A) (by parley_side) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_less (x := B) (y := abs A) (by parley_side) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := B) (y := abs A) (by parley_side) (by parley_side))).mp (by parley_side); parley_side)
        -- 6.3.3. substitute |A|² = A² (line 2) into line 6.3.2
        have s6_3_3 : B ^ 2 < A ^ 2 := by parley_subst_at s2 s6_3_2
        -- 6.3.4. inequalities, from 6.3.3
        have s6_3_4 : ¬ A ^ 2 ≤ B ^ 2 := by parley_side
        all_goals parley_side
      -- 6.4. inequalities, from 1
      have s6_4 : A ≤ abs A := by parley_side
      -- 6.5. transitivity, from 6.4, 6.3
      have s6_5 : A ≤ B := by parley_side
      -- 6.6. inequalities, from 1
      have s6_6 : -A ≤ abs A := by parley_side
      -- 6.7. transitivity, from 6.6, 6.3
      have s6_7 : -A ≤ B := by parley_side
      -- 6.8. join 6.5, 6.7
      have s6_8 : A ≤ B ∧ -A ≤ B := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.BoundedBySquare.BoundedBySquare
