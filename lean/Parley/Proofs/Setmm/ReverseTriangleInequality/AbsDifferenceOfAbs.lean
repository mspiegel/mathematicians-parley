module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow

/-! Written from proofs/setmm/reverse-triangle-inequality.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceOfAbs

theorem abs_difference_of_abs (A : ℝ) (B : ℝ) :
    abs (abs A - abs B) ≤ abs (A - B) := by
  -- 1. thm:abs-difference-below
  have s1 : abs A - abs B ≤ abs (A - B) := by first | linarith [(Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow.abs_difference_below (A := A) (B := B))] | (have h := (Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow.abs_difference_below (A := A) (B := B)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow.abs_difference_below (A := A) (B := B)) | (have h := (Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow.abs_difference_below (A := A) (B := B)); parley_side)
  -- 2. thm:abs-difference-below A := B, B := A
  have s2 : abs B - abs A ≤ abs (B - A) := by first | linarith [(Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow.abs_difference_below (A := B) (B := A))] | (have h := (Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow.abs_difference_below (A := B) (B := A)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow.abs_difference_below (A := B) (B := A)) | (have h := (Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow.abs_difference_below (A := B) (B := A)); parley_side)
  -- 3. mun:abs-negative x := A − B
  have s3 : abs (-(A - B)) = abs (A - B) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B)); parley_side)
  -- 4. substitute
  have s4 : abs (B - A) = abs (A - B) := by
    have c1 : -(A - B) = B - A := by parley_ring
    have row1 : abs (B - A) = abs (A - B) := by parley_subst_at c1 s3
    exact row1
  -- 5. substitute |B − A| = |A − B| (line 4) into line 2
  have s5 : abs B - abs A ≤ abs (A - B) := by parley_subst_at s4 s2
  -- 6. mun:nonneg-or-neg x := |A| − |B|
  have s6 : abs A - abs B ≥ 0 ∨ abs A - abs B < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := abs A - abs B)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := abs A - abs B))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := abs A - abs B)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := abs A - abs B)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := abs A - abs B)); parley_side)
  -- 7. cases, from 6
  have s7 : abs (abs A - abs B) ≤ abs (A - B) := by
    rcases s6 with hC1 | hC2
    · skip
      -- 7.1. def:abs x := |A| − |B|, from C1
      have s7_1 : abs (abs A - abs B) = abs A - abs B := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) (by parley_side); parley_side)
      -- 7.2. transitivity, from 7.1, 1
      have s7_2 : abs (abs A - abs B) ≤ abs (A - B) := by parley_side
      all_goals parley_side
    · skip
      -- 7.3. def:abs x := |A| − |B|, from C2
      have s7_3 : abs (abs A - abs B) = -(abs A - abs B) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) (by parley_side); parley_side)
      -- 7.4. inequalities
      have s7_4 : -(abs A - abs B) ≤ abs (A - B) := by parley_side
      -- 7.5. transitivity, from 7.3, 7.4
      have s7_5 : abs (abs A - abs B) ≤ abs (A - B) := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceOfAbs
