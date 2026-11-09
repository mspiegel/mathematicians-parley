module

public import AlgebraTactics
public import ArithTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/log-base-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.LogBaseLaws.LogOfAReciprocal

theorem log_of_a_reciprocal (x : ℝ) (b : ℝ) (hH3 : x > 0) (hH4 : b > 0) (hH5 : b ≠ 1) :
    Real.log (1 / x) / Real.log b = -(Real.log x / Real.log b) := by
  -- 1. mun:ln-quotient x := 1, y := x, from H3
  have r61_1 : (1 : ℤ) > 0 := by parley_arith
  have s1 : Real.log (1 / x) = Real.log (1 : ℝ) - Real.log x := by exact (Parley.Items.Stdlib.Logarithms.mun_ln_quotient (x := (1 : ℝ)) (y := x) (by parley_side) hH3)
  -- 2. substitute ln(1) = 0 (real arithmetic) into line 1
  have s2 : Real.log (1 / x) = 0 - Real.log x := by parley_subst_at (show Real.log (1 : ℝ) = 0 by parley_real) s1
  -- 3. mun:ln-nonzero x := b, from H4, H5
  have s3 : Real.log b ≠ 0 := by exact (Parley.Items.Stdlib.Logarithms.mun_ln_nonzero (x := b) hH4 hH5)
  -- 4. calculation
  calc Real.log (1 / x) / Real.log b = (0 - Real.log x) / Real.log b := by parley_subst s2
    _ = -(Real.log x / Real.log b) := by parley_ring

end Parley.Proofs.Identities.LogBaseLaws.LogOfAReciprocal
