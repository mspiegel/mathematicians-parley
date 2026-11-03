module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/difference-of-magnitudes.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceOfMagnitudes.DifferenceOfMagnitudes

theorem difference_of_magnitudes (A : ℝ) (B : ℝ) :
    abs (abs A - abs B) ≤ abs (A - B) := by
  -- 1. thm:triangle-inequality a := A − B, b := B
  have s1 : abs (A - B + B) ≤ abs (A - B) + abs B := by first | linarith [(Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B))] | (have h := (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B)) | (have h := (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B)); parley_side)
  -- 2. substitute
  have s2 : abs A ≤ abs (A - B) + abs B := by
    have c1 : A - B + B = A := by parley_ring
    have row1 : abs A ≤ abs (A - B) + abs B := by parley_subst_at c1 s1
    exact row1
  -- 3. thm:triangle-inequality a := B − A, b := A
  have s3 : abs (B - A + A) ≤ abs (B - A) + abs A := by first | linarith [(Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := B - A) (b := A))] | (have h := (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := B - A) (b := A)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := B - A) (b := A)) | (have h := (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := B - A) (b := A)); parley_side)
  -- 4. substitute
  have s4 : abs B ≤ abs (B - A) + abs A := by
    have c1 : B - A + A = B := by parley_ring
    have row1 : abs B ≤ abs (B - A) + abs A := by parley_subst_at c1 s3
    exact row1
  -- 5. mun:abs-negative x := A − B
  have s5 : abs (-(A - B)) = abs (A - B) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)); parley_side)
  -- 6. substitute
  have s6 : abs (B - A) = abs (A - B) := by
    have c1 : -(A - B) = B - A := by parley_ring
    have row1 : abs (B - A) = abs (A - B) := by parley_subst_at c1 s5
    exact row1
  -- 7. mun:nonneg-or-neg x := |A| − |B|
  have s7 : abs A - abs B ≥ 0 ∨ abs A - abs B < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := abs A - abs B)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := abs A - abs B))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := abs A - abs B)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := abs A - abs B)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := abs A - abs B)); parley_side)
  -- 8. cases, from 7
  have s8 : abs (abs A - abs B) ≤ abs (A - B) := by
    rcases s7 with hC1 | hC2
    · skip
      -- 8.1. inequalities
      have s8_1 : abs A - abs B ≤ abs (A - B) := by parley_order
      -- 8.2. calculation
      have s8_2 : abs (abs A - abs B) ≤ abs (A - B) := by
        calc abs (abs A - abs B) = abs A - abs B := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side); parley_side)
          _ ≤ abs (A - B) := by parley_side
      all_goals parley_side
    · skip
      -- 8.3. substitute |B − A| = |A − B| (line 6) into line 4
      have s8_3 : abs B ≤ abs (A - B) + abs A := by parley_subst_at s6 s4
      -- 8.4. inequalities
      have s8_4 : -(abs A - abs B) ≤ abs (A - B) := by parley_order
      -- 8.5. calculation
      have s8_5 : abs (abs A - abs B) ≤ abs (A - B) := by
        calc abs (abs A - abs B) = -(abs A - abs B) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side); parley_side)
          _ ≤ abs (A - B) := by parley_side
      all_goals parley_side
  all_goals exact s8

end Parley.Proofs.Setmm.DifferenceOfMagnitudes.DifferenceOfMagnitudes
