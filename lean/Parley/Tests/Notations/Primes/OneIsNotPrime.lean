module

public import ArithTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/notations/primes.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Primes.OneIsNotPrime

theorem one_is_not_prime :
    ¬ Nat.Prime (1 : ℤ).toNat := by
  -- 1. arithmetic
  have s1 : ¬ (1 : ℤ) > 1 := by parley_arith
  -- 2. contradiction
  have s2 : ¬ Nat.Prime (1 : ℤ).toNat := by
    by_contra hc_hS
    have hS : Nat.Prime (1 : ℤ).toNat := by parley_suppose hc_hS
    -- 2.1. def:prime p := 1, from S
    have s2_1 : (1 : ℤ) > 1 := by first | linarith [((Parley.Items.Stdlib.Divisibility.def_prime (p := 1) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := 1) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.def_prime (p := 1) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Divisibility.def_prime (p := 1) (by parley_side))).mp (by parley_side); parley_side)
    all_goals parley_side
  all_goals exact s2

end Parley.Tests.Notations.Primes.OneIsNotPrime
