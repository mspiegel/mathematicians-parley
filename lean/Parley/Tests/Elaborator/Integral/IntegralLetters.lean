module

public import Tactics

/-! Written from tests/elaborator/integral.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Integral.IntegralLetters

theorem integral_letters (a : ℝ) (b : ℝ) (x : ℝ) :
    (∫ s in a..b, (x * s : ℝ)) = (∫ u in a..b, (x * u : ℝ)) := by
  set I : ℝ := ∫ s in a..b, (x * s : ℝ) with hD1
  -- 1. D1
  have s1 : I = (∫ u in a..b, (x * u : ℝ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.Integral.IntegralLetters
