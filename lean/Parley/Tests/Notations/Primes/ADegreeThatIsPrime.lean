module

public import Tactics

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.ADegreeThatIsPrime

theorem a_degree_that_is_prime (m : ℤ) (hH1 : 0 < m) (hH2 : m = 97) :
    Nat.Prime m.toNat := by
  -- 1. inspection, from H2
  have s1 : Nat.Prime m.toNat := by parley_side
  all_goals exact s1

end Parley.Tests.Notations.Primes.ADegreeThatIsPrime
