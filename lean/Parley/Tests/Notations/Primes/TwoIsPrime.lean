module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.TwoIsPrime

theorem two_is_prime :
    Nat.Prime (2 : ℤ).toNat := by
  -- 1. mun:two-prime
  have s1 : Nat.Prime (2 : ℤ).toNat := by exact Parley.Items.Stdlib.Divisibility.mun_two_prime
  all_goals exact s1

end Parley.Tests.Notations.Primes.TwoIsPrime
