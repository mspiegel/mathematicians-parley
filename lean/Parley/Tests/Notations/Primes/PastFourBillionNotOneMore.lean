module

public import ArithTactics
public import Tactics

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.PastFourBillionNotOneMore

theorem past_four_billion_not_one_more :
    (2 ^ 32 + 1 : ℤ) ≠ 641 * 6700417 + 1 := by
  -- 1. arithmetic
  have s1 : (2 ^ 32 + 1 : ℤ) ≠ 641 * 6700417 + 1 := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Primes.PastFourBillionNotOneMore
