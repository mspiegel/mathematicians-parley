module

public import Tactics

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.NinetySevenIsPrime

theorem ninety_seven_is_prime :
    Nat.Prime 97 := by
  -- 1. inspection
  have s1 : Nat.Prime 97 := by parley_side
  all_goals parley_side

end Parley.Tests.Notations.Primes.NinetySevenIsPrime
