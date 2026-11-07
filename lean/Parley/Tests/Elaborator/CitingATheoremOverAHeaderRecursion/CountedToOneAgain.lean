module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne

/-! Written from tests/elaborator/citing-a-theorem-over-a-header-recursion.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOneAgain

theorem counted_to_one_again (F : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ ∀ n : ℤ, 0 ≤ n → F (n + 1) = F n + 1) :
    F 1 = 1 := by
  -- 1. thm:counted-to-one
  have s1 : F 1 = 1 := by exact (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne.counted_to_one (F := F) (by parley_side))
  all_goals exact s1

end Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOneAgain
