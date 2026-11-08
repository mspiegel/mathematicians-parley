module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum

/-! Written from tests/elaborator/a-cited-hypothesis-an-identity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorAtZero

theorem successor_at_zero :
    (2 * 1 : ℤ) = 2 * 0 + 2 := by
  -- 1. thm:successor-sum i := 0, j := 1
  exact (Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum.successor_sum (i := (0 : ℤ)) (by parley_side) (j := (1 : ℤ)) (by parley_side) (by parley_side))

end Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorAtZero
