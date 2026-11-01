module

public import Parley.Library

/-! Written from tests/elaborator/constant-left-over.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ConstantLeftOver.OneEquationAndAConstant

theorem one_equation_and_a_constant (s : ℝ) (H2 : s = 1) :
    s ≥ 0 := by
  -- 1. inequalities
  have s1 : s ≥ 1 := by parley_side
  -- 2. inequalities, from 1
  have s2 : s ≥ 0 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ConstantLeftOver.OneEquationAndAConstant
