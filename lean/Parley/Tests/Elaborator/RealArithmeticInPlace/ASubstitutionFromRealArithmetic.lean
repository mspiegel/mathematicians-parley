module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic-in-place.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticInPlace.ASubstitutionFromRealArithmetic

theorem a_substitution_from_real_arithmetic (a : ℝ) (H2 : a = Real.sqrt (8 : ℝ)) :
    a = 2 * Real.sqrt (2 : ℝ) := by
  -- 1. substitute √8 = 2·√2 (real arithmetic) into H2
  have s1 : a = 2 * Real.sqrt (2 : ℝ) := by parley_subst_at (show Real.sqrt (8 : ℝ) = 2 * Real.sqrt (2 : ℝ) by parley_side) H2
  parley_side

end Parley.Tests.Elaborator.RealArithmeticInPlace.ASubstitutionFromRealArithmetic
