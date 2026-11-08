module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.ADegreeThatIsPrime

theorem a_degree_that_is_prime (m : ℤ) (hH1 : 0 < m) (hH2 : m = 97) :
    Nat.Prime m.toNat := by
  -- 1. inspection, from H2
  parley_side

end Parley.Tests.Notations.Primes.ADegreeThatIsPrime
