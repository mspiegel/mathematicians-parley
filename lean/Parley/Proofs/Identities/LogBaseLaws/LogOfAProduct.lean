module

public import AlgebraTactics
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/log-base-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseLaws.LogOfAProduct

theorem log_of_a_product (x : ℝ) (y : ℝ) (b : ℝ) (hH4 : x > 0) (hH5 : y > 0) (hH6 : b > 0) (hH7 : b ≠ 1) :
    Real.log (x * y) / Real.log b = Real.log x / Real.log b + Real.log y / Real.log b := by
  -- 1. mun:ln-product, from H4, H5
  have s1 : Real.log (x * y) = Real.log x + Real.log y := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); parley_side)
  -- 2. mun:ln-nonzero x := b, from H6, H7
  have s2 : Real.log b ≠ 0 := by first | exact (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) hH7) | exact ((Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) hH7)).symm | simpa using (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) hH7) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) hH7) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) (by parley_side) hH7); parley_side)
  -- 3. calculation
  have s3 : Real.log (x * y) / Real.log b = Real.log x / Real.log b + Real.log y / Real.log b := by
    calc Real.log (x * y) / Real.log b = (Real.log x + Real.log y) / Real.log b := by parley_subst s1
      _ = Real.log x / Real.log b + Real.log y / Real.log b := by parley_ring
  all_goals exact s3

end Parley.Proofs.Identities.LogBaseLaws.LogOfAProduct
