module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/floor-in-a-bound.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FloorInABound.ARoundingErrorAtMostAHalf

theorem a_rounding_error_at_most_a_half (A : ℝ) (hH2 : (⌊A + 1 / 2⌋ : ℝ) - A ≥ 0) (hH3 : (⌊A + 1 / 2⌋ : ℝ) - A ≤ 1 / 2) :
    abs ((⌊A + 1 / 2⌋ : ℝ) - A) ≤ 1 / 2 := by
  -- 1. mun:floor-integer x := A + 1/2
  -- 2. membership, from 1
  -- 3. def:abs x := ⌊A + 1/2⌋ − A, from H2, 2
  have s3 : abs ((⌊A + 1 / 2⌋ : ℝ) - A) = (⌊A + 1 / 2⌋ : ℝ) - A := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) (by parley_side); parley_side)
  -- 4. transitivity, from 3, H3
  have s4 : abs ((⌊A + 1 / 2⌋ : ℝ) - A) ≤ 1 / 2 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.FloorInABound.ARoundingErrorAtMostAHalf
