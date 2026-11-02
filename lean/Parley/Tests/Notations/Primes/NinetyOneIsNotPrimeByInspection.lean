module

public import Tactics

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.NinetyOneIsNotPrimeByInspection

theorem ninety_one_is_not_prime_by_inspection :
    ¬ Nat.Prime 91 := by
  -- 1. inspection
  have s1 : ¬ Nat.Prime 91 := by parley_side
  all_goals parley_side

end Parley.Tests.Notations.Primes.NinetyOneIsNotPrimeByInspection
