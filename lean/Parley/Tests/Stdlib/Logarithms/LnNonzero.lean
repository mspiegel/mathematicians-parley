module

public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnNonzero

theorem ln_nonzero (x : ℝ) (hH2 : x > 0) (hH3 : x ≠ 1) :
    Real.log x ≠ 0 := by
  -- 1. mun:logarithms-ln-nonzero, from H2, H3
  have s1 : Real.log x ≠ 0 := by first | exact (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := x) (by parley_side) hH3) | exact ((Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := x) (by parley_side) hH3)).symm | simpa using (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := x) (by parley_side) hH3) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := x) (by parley_side) hH3) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := x) (by parley_side) hH3); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Logarithms.LnNonzero
