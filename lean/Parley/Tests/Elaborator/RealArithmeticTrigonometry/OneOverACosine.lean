module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.OneOverACosine

theorem one_over_a_cosine :
    Real.cos Real.pi ^ (-1 : ℤ) = -1 := by
  -- 1. real arithmetic
  have s1 : Real.cos Real.pi ^ (-1 : ℤ) = -1 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.OneOverACosine
