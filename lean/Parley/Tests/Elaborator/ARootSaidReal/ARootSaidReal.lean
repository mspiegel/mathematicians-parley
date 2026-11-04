module

public import OrderTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-root-said-real.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARootSaidReal.ARootSaidReal

theorem a_root_said_real (A : ℝ) (hH2 : A ≥ 0) :
    Real.sqrt A ^ 2 ≤ A + 1 := by
  -- 1. def:sqrt x := A, from H2
  have s1 : Real.sqrt A ^ 2 = A := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) (by parley_side)); parley_side)
  -- 2. inequalities
  have s2 : A ≤ A + 1 := by parley_order
  -- 3. transitivity, from 1, 2
  have s3 : Real.sqrt A ^ 2 ≤ A + 1 := by parley_order
  all_goals exact s3

end Parley.Tests.Elaborator.ARootSaidReal.ARootSaidReal
