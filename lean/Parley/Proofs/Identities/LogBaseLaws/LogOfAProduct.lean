module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/log-base-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseLaws.LogOfAProduct

theorem log_of_a_product (x : ℝ) (y : ℝ) (b : ℝ) (hH4 : x > 0) (hH5 : y > 0) (hH6 : b > 0) (hH7 : b ≠ 1) :
    Real.log (x * y) / Real.log b = Real.log x / Real.log b + Real.log y / Real.log b := by
  -- 1. mun:ln-product, from H4, H5
  have s1 : Real.log (x * y) = Real.log x + Real.log y := by exact (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) hH4 hH5)
  -- 2. mun:ln-nonzero x := b, from H6, H7
  have s2 : Real.log b ≠ 0 := by exact (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) hH6 hH7)
  -- 3. calculation
  calc Real.log (x * y) / Real.log b = (Real.log x + Real.log y) / Real.log b := by (have h := congrArg (fun t : ℝ => t / Real.log b) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Real.log x / Real.log b + Real.log y / Real.log b := by parley_ring

end Parley.Proofs.Identities.LogBaseLaws.LogOfAProduct
