module

public import Tactics

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.ADegreeThatIsPrime

theorem a_degree_that_is_prime (m : ℕ) (hH1 : 0 < m) (hH2 : (m : ℤ) = 97) :
    Nat.Prime m := by
  -- 1. inspection, from H2
  have s1 : Nat.Prime m := by parley_side
  all_goals parley_side

end Parley.Tests.Notations.Primes.ADegreeThatIsPrime
