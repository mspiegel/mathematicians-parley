module

public import AlgebraTactics
public import Tactics

/-! Written from tests/elaborator/a-cited-conclusion-without-its-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor

theorem doubled_successor (n : ℤ) (hH1 : 0 ≤ n) :
    2 * (n + 1) = 2 * n + 2 := by
  -- 1. calculation
  have s1 : 2 * (n + 1) = 2 * n + 2 := by
    calc 2 * (n + 1) = 2 * (n + 1) := by parley_side
      _ = 2 * n + 2 := by parley_ring
      _ = 2 * n + 2 := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ACitedConclusionWithoutItsZero.DoubledSuccessor
