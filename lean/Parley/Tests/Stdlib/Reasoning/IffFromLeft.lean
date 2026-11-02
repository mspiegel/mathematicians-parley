module

public import Tactics
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.IffFromLeft

theorem iff_from_left (x : ℝ) (hH2 : x = 0 ↔ x ^ 2 = 0) (hH3 : x = 0) :
    x ^ 2 = 0 := by
  -- 1. mun:reasoning-iff-from-left, from H2, H3
  have s1 : x ^ 2 = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_from_left (P := x = 0) (Q := x ^ 2 = 0) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Reasoning.IffFromLeft
