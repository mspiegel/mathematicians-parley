module

public import Tactics

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.PastFourBillion

theorem past_four_billion :
    (641 : ℤ) ∣ (2 ^ 32 + 1 : ℤ) := by
  -- 1. arithmetic
  have s1 : (641 : ℤ) ∣ (2 ^ 32 + 1 : ℤ) := by parley_arith
  all_goals parley_side

end Parley.Tests.Notations.Primes.PastFourBillion
