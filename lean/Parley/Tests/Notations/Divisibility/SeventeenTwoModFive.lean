module

public import ArithTactics
public import Tactics

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.SeventeenTwoModFive

theorem seventeen_two_mod_five :
    (17 : ℤ) ≡ (2 : ℤ) [ZMOD (5 : ℤ)] := by
  -- 1. arithmetic
  have s1 : (17 : ℤ) ≡ (2 : ℤ) [ZMOD (5 : ℤ)] := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Divisibility.SeventeenTwoModFive
