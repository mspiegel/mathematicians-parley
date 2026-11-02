module

public import LeanBridges

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.PastFourBillionExactly

theorem past_four_billion_exactly :
    (2 ^ 32 + 1 : ℤ) = 641 * 6700417 := by
  -- 1. arithmetic
  have s1 : (2 ^ 32 + 1 : ℤ) = 641 * 6700417 := by parley_arith
  all_goals parley_side

end Parley.Tests.Notations.Primes.PastFourBillionExactly
