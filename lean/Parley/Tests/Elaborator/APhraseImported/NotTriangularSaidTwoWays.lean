module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init

/-! Written from tests/elaborator/a-phrase-imported.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseImported.NotTriangularSaidTwoWays

theorem not_triangular_said_two_ways (hH1 : ¬ ((0 : ℤ) < 4 ∧ (∃ k : ℤ, 0 < k ∧ 4 = (k : ℚ) * ((k : ℚ) + 1) / 2))) :
    ¬ ((0 : ℤ) < 4 ∧ (∃ k : ℤ, 0 < k ∧ 4 = (k : ℚ) * ((k : ℚ) + 1) / 2)) := by
  -- 1. restate H1
  have s1 : ¬ ((0 : ℤ) < 4 ∧ (∃ k : ℤ, 0 < k ∧ 4 = (k : ℚ) * ((k : ℚ) + 1) / 2)) := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.APhraseImported.NotTriangularSaidTwoWays
