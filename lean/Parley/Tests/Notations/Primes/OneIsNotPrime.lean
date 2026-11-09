module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.OneIsNotPrime

theorem one_is_not_prime :
    ¬ Nat.Prime (1 : ℤ).toNat := by
  -- 1. arithmetic
  have s1 : ¬ (1 : ℤ) > 1 := by parley_arith
  -- 2. contradiction
  intro hS
  -- 2.1. def:prime p := 1, from S
  have s2_1 : (1 : ℤ) > 1 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := (1 : ℤ)) (by parley_side))).mp hS).1
  exact s1 s2_1

end Parley.Tests.Notations.Primes.OneIsNotPrime
