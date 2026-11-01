module

public import Parley.Library

/-! Written from tests/elaborator/closed-pieces.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedPieces.AFactorialLinkOfNumerals

theorem a_factorial_link_of_numerals :
    (Parley.Library.factorial (2 : ℤ) : ℤ) = (Parley.Library.factorial (1 + 1 : ℤ) : ℤ) := by
  -- 1. calculation
  have s1 : (Parley.Library.factorial (2 : ℤ) : ℤ) = (Parley.Library.factorial (1 + 1 : ℤ) : ℤ) := by norm_num
  all_goals parley_side

end Parley.Tests.Elaborator.ClosedPieces.AFactorialLinkOfNumerals
