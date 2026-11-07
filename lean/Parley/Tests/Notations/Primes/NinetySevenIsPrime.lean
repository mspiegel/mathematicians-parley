module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Prime

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.NinetySevenIsPrime

theorem ninety_seven_is_prime :
    Nat.Prime (97 : ℤ).toNat := by
  -- 1. inspection
  have s1 : Nat.Prime (97 : ℤ).toNat := by parley_side
  all_goals exact s1

end Parley.Tests.Notations.Primes.NinetySevenIsPrime
