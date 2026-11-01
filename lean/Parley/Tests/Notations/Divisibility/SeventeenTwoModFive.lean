module

public import Parley.Library

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.SeventeenTwoModFive

theorem seventeen_two_mod_five :
    (17 : ℤ) ≡ (2 : ℤ) [ZMOD (5 : ℤ)] := by
  -- 1. arithmetic
  have s1 : (17 : ℤ) ≡ (2 : ℤ) [ZMOD (5 : ℤ)] := by norm_num
  parley_side

end Parley.Tests.Notations.Divisibility.SeventeenTwoModFive
