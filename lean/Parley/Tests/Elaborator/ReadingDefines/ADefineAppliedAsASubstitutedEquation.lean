module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedAsASubstitutedEquation

theorem a_define_applied_as_a_substituted_equation (a : ℤ) (hH1 : 0 < a) (q : ℤ → ℤ) (hD1 : ∀ j : ℤ, 0 < j → q j = j + 1) :
    q a * 2 = (a + 1) * 2 := by
  -- 1. substitute q(a) = a + 1 (D1)
  (have h := congrArg (fun t : ℤ => t * 2) (hD1 _ hH1); push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedAsASubstitutedEquation
