module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-requires-weakening-with-its-membership.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARequiresWeakeningWithItsMembership.ARequiresWeakeningWithItsMembership

theorem a_requires_weakening_with_its_membership (x : ℝ) (hH2 : x ≥ 0) :
    Real.sqrt (x + 1) - Real.sqrt x = 1 / (Real.sqrt (x + 1) + Real.sqrt x) := by
  -- 1. inequalities, from H2
  have s1 : x + 1 ≥ 0 := by parley_side
  -- 2. def:sqrt x := x + 1, from 1
  have s2a : Real.sqrt (x + 1) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x + 1) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x + 1) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x + 1) (by parley_side)); parley_side)
  have s2b : Real.sqrt (x + 1) ^ 2 = x + 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x + 1) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x + 1) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x + 1) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x + 1) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x + 1) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x + 1) (by parley_side)); parley_side)
  -- 3. def:sqrt, from H2
  have s3a : Real.sqrt x ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := x) (by parley_side)); parley_side)
  have s3b : Real.sqrt x ^ 2 = x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := x) (by parley_side)); parley_side)
  -- 4. inequalities
  have s4 : x < x + 1 := by parley_side
  -- 5. calculation
  have s5 : Real.sqrt x ^ 2 < Real.sqrt (x + 1) ^ 2 := by
    calc Real.sqrt x ^ 2 = x := by parley_side
      _ < x + 1 := by parley_side
      _ = Real.sqrt (x + 1) ^ 2 := by parley_side
  -- 6. mun:square-less x := √x, y := √(x + 1), from 2, 3, 5
  have s6 : Real.sqrt x < Real.sqrt (x + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt x) (y := Real.sqrt (x + 1)) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt x) (y := Real.sqrt (x + 1)) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
  -- 7. transitivity, from 3, 6
  have s7 : Real.sqrt (x + 1) > 0 := by parley_side
  -- 8. inequalities, from 2, 3, 7
  have s8 : Real.sqrt (x + 1) + Real.sqrt x > 0 := by parley_side
  -- 9. algebra, from 2, 3
  have r40_3 : Real.sqrt (x + 1) + Real.sqrt x ≠ 0 := by parley_side
  have s9 : Real.sqrt (x + 1) - Real.sqrt x = 1 / (Real.sqrt (x + 1) + Real.sqrt x) := by linear_combination (norm := parley_field) ((1) / ((Real.sqrt (x + 1) + Real.sqrt x))) * s2b + ((-1) / ((Real.sqrt (x + 1) + Real.sqrt x))) * s3b
  all_goals parley_side

end Parley.Tests.Elaborator.ARequiresWeakeningWithItsMembership.ARequiresWeakeningWithItsMembership
