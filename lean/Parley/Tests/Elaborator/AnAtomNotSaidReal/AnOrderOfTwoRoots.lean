module

public import OrderTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/an-atom-not-said-real.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnAtomNotSaidReal.AnOrderOfTwoRoots

theorem an_order_of_two_roots (A : ℝ) (B : ℝ) (hH3 : 0 ≤ A) (hH4 : 0 ≤ B) (hH5 : ¬ Real.sqrt A ≤ Real.sqrt B) :
    Real.sqrt B < Real.sqrt A := by
  -- 1. def:sqrt x := A, from H3
  have s1a : Real.sqrt A ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) hH3)] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) hH3); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) hH3) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) hH3); parley_side)
  have s1b : Real.sqrt A ^ 2 = A := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3); parley_side)
  -- 2. def:sqrt x := B, from H4
  have s2a : Real.sqrt B ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) hH4)] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) hH4); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) hH4) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) hH4); parley_side)
  have s2b : Real.sqrt B ^ 2 = B := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4); parley_side)
  -- 3. inequalities, from H5
  have s3 : Real.sqrt B < Real.sqrt A := by parley_order
  all_goals exact s3

end Parley.Tests.Elaborator.AnAtomNotSaidReal.AnOrderOfTwoRoots
