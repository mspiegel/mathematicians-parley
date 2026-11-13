module

public import AlgebraTactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedInACalculationLink

theorem a_define_applied_in_a_calculation_link (a : ℤ) (hH1 : 0 < a) (q : ℤ → ℤ) (hD1 : ∀ j : ℤ, 0 < j → q j = j + 1) :
    q a + 1 = a + 2 := by
  -- 1. algebra
  have s1 : a + 1 + 1 = a + 2 := by parley_ring
  -- 2. calculation
  calc q a + 1 = a + 1 + 1 := by simp (disch := omega) only [hD1]
    _ = a + 2 := s1

end Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedInACalculationLink
