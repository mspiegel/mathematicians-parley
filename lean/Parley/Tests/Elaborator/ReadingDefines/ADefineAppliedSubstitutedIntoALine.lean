module

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

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedSubstitutedIntoALine

theorem a_define_applied_substituted_into_a_line (a : ℤ) (hH1 : 0 < a) (q : ℤ → ℤ) (hD1 : ∀ j : ℤ, 0 < j → q j = j + 1) (hH2 : q a > 3) :
    a + 1 > 3 := by
  -- 1. substitute q(a) = a + 1 (D1) into H2
  (have h := Eq.subst (motive := (fun t : ℤ => t > 3)) (hD1 _ hH1) hH2; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Tests.Elaborator.ReadingDefines.ADefineAppliedSubstitutedIntoALine
