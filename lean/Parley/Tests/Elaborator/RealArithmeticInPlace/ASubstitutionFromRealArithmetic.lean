module

public import RealTactics
public import SubstTactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-in-place.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticInPlace.ASubstitutionFromRealArithmetic

theorem a_substitution_from_real_arithmetic (a : ℝ) (hH2 : a = Real.sqrt (8 : ℝ)) :
    a = 2 * Real.sqrt (2 : ℝ) := by
  -- 1. substitute √8 = 2·√2 (real arithmetic) into H2
  parley_subst_at (show Real.sqrt (8 : ℝ) = 2 * Real.sqrt (2 : ℝ) by parley_real) hH2

end Parley.Tests.Elaborator.RealArithmeticInPlace.ASubstitutionFromRealArithmetic
