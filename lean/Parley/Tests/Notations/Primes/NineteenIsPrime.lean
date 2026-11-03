module

public import Tactics

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.NineteenIsPrime

theorem nineteen_is_prime :
    Nat.Prime 19 := by
  -- 1. inspection
  have s1 : Nat.Prime 19 := by parley_side
  all_goals exact s1

end Parley.Tests.Notations.Primes.NineteenIsPrime
