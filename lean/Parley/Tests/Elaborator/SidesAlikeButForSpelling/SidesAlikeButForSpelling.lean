module

public import Tactics

/-! Written from tests/elaborator/sides-alike-but-for-spelling.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SidesAlikeButForSpelling.SidesAlikeButForSpelling

theorem sides_alike_but_for_spelling (A : ℝ) (B : ℝ) :
    ¬ A < B + (A - B) := by
  -- 1. inequalities
  have s1 : ¬ A < B + (A - B) := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.SidesAlikeButForSpelling.SidesAlikeButForSpelling
