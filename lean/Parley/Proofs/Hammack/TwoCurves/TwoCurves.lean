module

public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Reasoning
public import Parley.Library

/-! Written from proofs/hammack/two-curves.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.TwoCurves.TwoCurves

theorem two_curves (x : ℝ) (y : ℝ) :
    (x ^ 3 + x ^ 2 * y = y ^ 2 + x * y ↔ y = x ^ 2 ∨ y = -x) := by
  -- the theorem. both directions
  have sThm : x ^ 3 + x ^ 2 * y = y ^ 2 + x * y ↔ y = x ^ 2 ∨ y = -x := by
    constructor
    · skip
      intro hD1
      -- 1. algebra, from D1
      have s1 : (y - x ^ 2) * (y + x) = 0 := by linear_combination (norm := parley_norm) (-1) * hD1
      -- 2. axi:excluded-middle P := y + x = 0
      have s2 : y + x = 0 ∨ y + x ≠ 0 := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := y + x = 0)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := y + x = 0))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := y + x = 0)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := y + x = 0))
      -- 3. cases, from 2
      have s3 : y = x ^ 2 ∨ y = -x := by
        rcases s2 with hC1 | hC2
        · skip
          -- 3.1. algebra, from C1
          have s3_1 : y = -x := by linear_combination (norm := parley_norm) hC1
          -- 3.2. mun:or-right, from 3.1
          have s3_2 : y = x ^ 2 ∨ y = -x := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := y = x ^ 2) (Q := y = -x) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := y = x ^ 2) (Q := y = -x) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := y = x ^ 2) (Q := y = -x) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := y = x ^ 2) (Q := y = -x) (by parley_side))
          all_goals parley_side
        · skip
          -- 3.3. algebra, from 1
          have s3_3 : (y - x ^ 2) * (y + x) = 0 * (y + x) := by linear_combination (norm := parley_norm) s1
          -- 3.4. mun:multiply-cancel a := y − x², b := 0, c := y + x, from C2, 3.3
          have s3_4 : y - x ^ 2 = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := y - x ^ 2) (b := (0 : ℝ)) (c := y + x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := y - x ^ 2) (b := (0 : ℝ)) (c := y + x) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := y - x ^ 2) (b := (0 : ℝ)) (c := y + x) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := y - x ^ 2) (b := (0 : ℝ)) (c := y + x) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := y - x ^ 2) (b := (0 : ℝ)) (c := y + x) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := y - x ^ 2) (b := (0 : ℝ)) (c := y + x) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h)
          -- 3.5. algebra, from 3.4
          have s3_5 : y = x ^ 2 := by linear_combination (norm := parley_norm) s3_4
          -- 3.6. mun:or-left, from 3.5
          have s3_6 : y = x ^ 2 ∨ y = -x := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := y = x ^ 2) (Q := y = -x) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := y = x ^ 2) (Q := y = -x) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := y = x ^ 2) (Q := y = -x) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := y = x ^ 2) (Q := y = -x) (by parley_side))
          all_goals parley_side
      all_goals parley_side
    · skip
      intro hD2
      -- 4. cases, from D2
      have s4 : x ^ 3 + x ^ 2 * y = y ^ 2 + x * y := by
        rcases hD2 with hC3 | hC4
        · skip
          -- 4.1. algebra, from C3
          have s4_1 : x ^ 3 + x ^ 2 * y = y ^ 2 + x * y := by linear_combination (norm := parley_norm) (-x - y) * hC3
          all_goals parley_side
        · skip
          -- 4.2. algebra, from C4
          have s4_2 : x ^ 3 + x ^ 2 * y = y ^ 2 + x * y := by linear_combination (norm := parley_norm) (x ^ 2 - y) * hC4
          all_goals parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.TwoCurves.TwoCurves
