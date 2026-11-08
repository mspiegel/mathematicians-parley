module

public import AlgebraTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedInACalculationLink

theorem a_define_applied_in_a_calculation_link (a : ℤ) (hH1 : 0 < a) (q : ℤ → ℤ) (hD1 : ∀ j : ℤ, 0 < j → q j = j + 1) :
    q a + 1 = a + 2 := by
  -- 1. algebra
  have s1 : a + 1 + 1 = a + 2 := by parley_ring
  -- 2. calculation
  calc q a + 1 = a + 1 + 1 := by simp (disch := omega) only [hD1]
    _ = a + 2 := by parley_side

end Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedInACalculationLink
