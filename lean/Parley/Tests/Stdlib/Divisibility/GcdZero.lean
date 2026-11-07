module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.GcdZero

theorem gcd_zero (n : ℤ) (hH1 : 0 ≤ n) :
    (Int.gcd n (0 : ℤ) : ℤ) = n := by
  -- 1. mun:divisibility-gcd-zero
  have s1 : (Int.gcd n (0 : ℤ) : ℤ) = n := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_zero (n := n) (by parley_side))
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.GcdZero
