module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.RealSqrt

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootOfARoot

theorem a_root_of_a_root :
    Real.sqrt (Real.sqrt (4 : ℝ)) = Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (Real.sqrt (4 : ℝ)) = Real.sqrt (2 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.ARootOfARoot
