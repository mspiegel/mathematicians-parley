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
public import Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFrom

/-! Written from tests/elaborator/citing-a-theorem-over-a-header-recursion.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFromALetter

theorem counted_on_from_a_letter (N : ℤ) (hH1 : 0 ≤ N) (F : ℤ → ℤ) (hD1 : F 0 = N ∧ (∀ j : ℤ, 0 ≤ j → F (j + 1) = F j + 1)) :
    F 1 = N + 1 := by
  -- 1. thm:counted-on-from M := N
  exact (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFrom.counted_on_from (M := N) hH1 (F := F) hD1)

end Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFromALetter
