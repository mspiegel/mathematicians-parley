module

public import AlgebraTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Core

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedInACalculationLink

theorem a_define_applied_in_a_calculation_link (a : ℤ) (hH1 : 0 < a) (q : ℤ → ℤ) (hD1 : ∀ j : ℤ, 0 < j → q j = j + 1) :
    q a + 1 = a + 2 := by
  -- 1. algebra
  have s1 : a + 1 + 1 = a + 2 := by parley_ring
  -- 2. calculation
  have s2 : q a + 1 = a + 2 := by
    calc q a + 1 = a + 1 + 1 := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      _ = a + 2 := by parley_side
  all_goals exact s2

end Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedInACalculationLink
