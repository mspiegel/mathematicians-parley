module

public import Tactics

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedInACalculationLink

theorem a_define_applied_in_a_calculation_link (a : ℕ) (hH1 : 0 < a) (q : ℤ → ℤ) (hD1 : ∀ j : ℤ, 0 < j → q j = j + 1) :
    q (a : ℤ) + 1 = (a : ℤ) + 2 := by
  -- 1. algebra
  have s1 : (a : ℤ) + 1 + 1 = (a : ℤ) + 2 := by parley_ring
  -- 2. calculation
  have s2 : q (a : ℤ) + 1 = (a : ℤ) + 2 := by
    calc q (a : ℤ) + 1 = (a : ℤ) + 1 + 1 := by first | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      _ = (a : ℤ) + 2 := by parley_side
  all_goals exact s2

end Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedInACalculationLink
