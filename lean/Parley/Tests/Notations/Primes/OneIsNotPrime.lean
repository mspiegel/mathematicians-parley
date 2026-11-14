module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.OneIsNotPrime

theorem one_is_not_prime :
    ¬ Nat.Prime (1 : ℤ).toNat := by
  -- 1. arithmetic
  have s1 : ¬ (1 : ℤ) > 1 := by norm_num
  -- 2. contradiction
  intro hS
  -- 2.1. def:prime p := 1, from S
  have s2_1 : (1 : ℤ) > 1 := by exact (((Parley.Items.Stdlib.Divisibility.def_prime (p := (1 : ℤ)) (by norm_num))).mp hS).1
  exact s1 s2_1

end Parley.Tests.Notations.Primes.OneIsNotPrime
