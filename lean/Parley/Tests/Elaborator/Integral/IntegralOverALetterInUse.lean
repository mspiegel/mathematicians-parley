module

public import Tactics

/-! Written from tests/elaborator/integral.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Integral.IntegralOverALetterInUse

theorem integral_over_a_letter_in_use (a : ℝ) (b : ℝ) (x : ℝ) :
    (∫ x in a..b, (x : ℝ)) = (∫ t in a..b, (t : ℝ)) := by
  set J : ℝ := ∫ x in a..b, (x : ℝ) with hD1
  -- 1. D1
  have s1 : J = (∫ t in a..b, (t : ℝ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.Integral.IntegralOverALetterInUse
