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
public import Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne

/-! Written from tests/elaborator/citing-a-theorem-over-a-header-recursion.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOneAgain

theorem counted_to_one_again (F : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ (∀ n : ℤ, 0 ≤ n → F (n + 1) = F n + 1)) :
    F 1 = 1 := by
  -- 1. thm:counted-to-one
  exact (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne.counted_to_one (F := F) hD1)

end Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOneAgain
