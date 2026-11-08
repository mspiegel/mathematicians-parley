module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Prime

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.NinetyOneIsNotPrimeByInspection

theorem ninety_one_is_not_prime_by_inspection :
    ¬ Nat.Prime (91 : ℤ).toNat := by
  -- 1. inspection
  parley_side

end Parley.Tests.Notations.Primes.NinetyOneIsNotPrimeByInspection
