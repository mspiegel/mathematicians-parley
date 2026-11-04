module

public import Tactics

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedAsASubstitutedEquation

theorem a_define_applied_as_a_substituted_equation (a : ℕ) (hH1 : 0 < a) (q : ℤ → ℤ) (hD1 : ∀ j : ℤ, 0 < j → q j = j + 1) :
    q (a : ℤ) * 2 = ((a : ℤ) + 1) * 2 := by
  -- 1. substitute q(a) = a + 1 (D1)
  have s1 : q (a : ℤ) * 2 = ((a : ℤ) + 1) * 2 := by (try simp only [hD1] at *); first | done | parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedAsASubstitutedEquation
