module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/log-base-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseLaws.ChangeOfBase

theorem change_of_base (x : ℝ) (b : ℝ) (c : ℝ) (hH4 : x > 0) (hH5 : b > 0) (hH6 : b ≠ 1) (hH7 : c > 0) (hH8 : c ≠ 1) :
    Real.log x / Real.log c / (Real.log b / Real.log c) = Real.log x / Real.log b := by
  -- 1. mun:ln-nonzero x := b, from H5, H6
  have s1 : Real.log b ≠ 0 := by exact (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) hH5 hH6)
  -- 2. mun:ln-nonzero x := c, from H7, H8
  have s2 : Real.log c ≠ 0 := by exact (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := c) hH7 hH8)
  -- 3. algebra, from 1, 2
  parley_ring

end Parley.Proofs.Identities.LogBaseLaws.ChangeOfBase
