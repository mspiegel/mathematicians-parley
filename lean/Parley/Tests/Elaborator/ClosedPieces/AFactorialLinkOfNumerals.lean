module

public import Counting
public import Tactics

/-! Written from tests/elaborator/closed-pieces.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedPieces.AFactorialLinkOfNumerals

theorem a_factorial_link_of_numerals :
    (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) := by
  -- 1. calculation
  have s1 : (LeanBridges.Counting.factorial (2 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) := by norm_num
  all_goals parley_side

end Parley.Tests.Elaborator.ClosedPieces.AFactorialLinkOfNumerals
