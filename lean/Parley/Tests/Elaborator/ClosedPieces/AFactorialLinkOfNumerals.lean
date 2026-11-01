module

public import Parley.Library

/-! Written from tests/elaborator/closed-pieces.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedPieces.AFactorialLinkOfNumerals

theorem a_factorial_link_of_numerals :
    (Nat.factorial 2 : ℤ) = (Nat.factorial (1 + 1) : ℤ) := by
  -- 1. calculation
  have s1 : (Nat.factorial 2 : ℤ) = (Nat.factorial (1 + 1) : ℤ) := by
    calc ((Nat.factorial 2 : ℤ) : ℤ) = (Nat.factorial (1 + 1) : ℤ) := by norm_num
  parley_side

end Parley.Tests.Elaborator.ClosedPieces.AFactorialLinkOfNumerals
