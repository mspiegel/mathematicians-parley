module

public import Tactics
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/log-base-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseLaws.ChangeOfBase

theorem change_of_base (x : ℝ) (b : ℝ) (c : ℝ) (hH4 : x > 0) (hH5 : b > 0) (hH6 : b ≠ 1) (hH7 : c > 0) (hH8 : c ≠ 1) :
    Real.log x / Real.log c / (Real.log b / Real.log c) = Real.log x / Real.log b := by
  -- 1. mun:ln-nonzero x := b, from H5, H6
  have s1 : Real.log b ≠ 0 := by first | exact (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) (by parley_side)); parley_side)
  -- 2. mun:ln-nonzero x := c, from H7, H8
  have s2 : Real.log c ≠ 0 := by first | exact (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := c) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := c) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := c) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := c) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := c) (by parley_side) (by parley_side)); parley_side)
  -- 3. algebra, from 1, 2
  have s3 : Real.log x / Real.log c / (Real.log b / Real.log c) = Real.log x / Real.log b := by parley_ring
  all_goals parley_side

end Parley.Proofs.Identities.LogBaseLaws.ChangeOfBase
