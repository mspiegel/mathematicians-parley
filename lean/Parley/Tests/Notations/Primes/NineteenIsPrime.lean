module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Prime

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.NineteenIsPrime

theorem nineteen_is_prime :
    Nat.Prime (19 : ℤ).toNat := by
  -- 1. inspection
  parley_side

end Parley.Tests.Notations.Primes.NineteenIsPrime
