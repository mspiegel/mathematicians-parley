module

public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ACubeOfAProductOfRoots

theorem a_cube_of_a_product_of_roots :
    (Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ)) ^ 3 = 6 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) := by
  -- 1. real arithmetic
  parley_real

end Parley.Tests.Elaborator.RealArithmetic.ACubeOfAProductOfRoots
