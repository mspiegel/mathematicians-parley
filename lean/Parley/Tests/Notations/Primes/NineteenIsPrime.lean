module

public import Parley.Library

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.NineteenIsPrime

theorem nineteen_is_prime :
    Nat.Prime 19 := by
  -- 1. inspection
  have s1 : Nat.Prime 19 := by parley_side
  parley_side

end Parley.Tests.Notations.Primes.NineteenIsPrime
