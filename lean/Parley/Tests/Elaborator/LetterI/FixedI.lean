module

public import LeanBridges

/-! Written from tests/elaborator/letter-i.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LetterI.FixedI

theorem fixed_i (i : ℕ) (hH1 : 0 < i) :
    (i : ℤ) ≥ 1 := by
  -- 1. inequalities, from H1
  have s1 : (i : ℤ) ≥ 1 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.LetterI.FixedI
