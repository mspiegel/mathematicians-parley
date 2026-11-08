module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootLessOneIsNotZero

theorem a_root_less_one_is_not_zero :
    Real.sqrt (2 : ℝ) - 1 ≠ 0 := by
  -- 1. real arithmetic
  parley_real

end Parley.Tests.Elaborator.RealArithmetic.ARootLessOneIsNotZero
