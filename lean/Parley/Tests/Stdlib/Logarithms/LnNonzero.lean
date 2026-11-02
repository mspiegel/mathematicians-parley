module

public import LeanBridges
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnNonzero

theorem ln_nonzero (x : ℝ) (hH2 : x > 0) (hH3 : x ≠ 1) :
    Real.log x ≠ 0 := by
  -- 1. mun:logarithms-ln-nonzero, from H2, H3
  have s1 : Real.log x ≠ 0 := by first | exact (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := x) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := x) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := x) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := x) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := x) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Logarithms.LnNonzero
