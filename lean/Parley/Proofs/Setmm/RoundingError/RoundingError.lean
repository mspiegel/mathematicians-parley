module

public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/rounding-error.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RoundingError.RoundingError

set_option maxHeartbeats 400000 in
theorem rounding_error (A : ℝ) :
    abs ((⌊A + 1 / 2⌋ : ℝ) - A) ≤ 1 / 2 := by
  -- 1. mun:floor-integer x := A + 1/2
  -- 2. mun:floor-below x := A + 1/2
  have s2 : (⌊A + 1 / 2⌋ : ℝ) ≤ A + 1 / 2 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_below (x := A + 1 / 2))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A + 1 / 2)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A + 1 / 2)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A + 1 / 2)); parley_side)
  -- 3. mun:floor-above x := A + 1/2
  have s3 : A + 1 / 2 < (⌊A + 1 / 2⌋ : ℝ) + 1 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_above (x := A + 1 / 2))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A + 1 / 2)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A + 1 / 2)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A + 1 / 2)); parley_side)
  set e : ℝ := (⌊A + 1 / 2⌋ : ℝ) - A with hD1
  have hD1_kind : True := by parley_side
  -- 4. inequalities
  have s4 : (⌊A + 1 / 2⌋ : ℝ) - A ≤ 1 / 2 := by parley_order
  -- 5. transitivity, from D1, 4
  have s5 : e ≤ 1 / 2 := by parley_order
  -- 6. inequalities
  have s6 : -(1 / 2) < (⌊A + 1 / 2⌋ : ℝ) - A := by parley_order
  -- 7. transitivity, from 6, D1
  have s7 : -(1 / 2) < e := by parley_order
  -- 8. inequalities
  have s8 : -e ≤ 1 / 2 := by parley_order
  -- 9. mun:nonneg-or-neg x := e, from D1
  have s9 : e ≥ 0 ∨ e < 0 := by
    try simp only [hD1] at *
    try push_cast at *
    first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := (⌊A + 1 / 2⌋ : ℝ) - A)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := (⌊A + 1 / 2⌋ : ℝ) - A))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := (⌊A + 1 / 2⌋ : ℝ) - A)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := (⌊A + 1 / 2⌋ : ℝ) - A)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := (⌊A + 1 / 2⌋ : ℝ) - A)); parley_side)
  -- 10. cases, from 9
  have s10 : abs e ≤ 1 / 2 := by
    rcases s9 with hC1 | hC2
    · skip
      -- 10.1. def:abs x := e, from C1, D1
      have s10_1 : abs e = e := by
        try simp only [hD1] at *
        try push_cast at *
        first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); parley_side)
      -- 10.2. transitivity, from 10.1, 5
      have s10_2 : abs e ≤ 1 / 2 := by parley_order
      all_goals parley_side
    · skip
      -- 10.3. def:abs x := e, from C2, D1
      have s10_3 : abs e = -e := by
        try simp only [hD1] at *
        try push_cast at *
        first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_2 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); parley_side)
      -- 10.4. transitivity, from 10.3, 8
      have s10_4 : abs e ≤ 1 / 2 := by parley_order
      all_goals parley_side
  -- 11. substitute e = ⌊A + 1/2⌋ − A (D1) into line 10
  have s11 : abs ((⌊A + 1 / 2⌋ : ℝ) - A) ≤ 1 / 2 := by parley_subst_at hD1 s10
  all_goals exact s11

end Parley.Proofs.Setmm.RoundingError.RoundingError
