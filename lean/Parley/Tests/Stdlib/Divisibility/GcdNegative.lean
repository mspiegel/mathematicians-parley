module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.GcdNegative

theorem gcd_negative (a : ℤ) (b : ℤ) :
    (Int.gcd (-a) b : ℤ) = (Int.gcd a b : ℤ) := by
  -- 1. mun:divisibility-gcd-negative
  have s1 : (Int.gcd (-a) b : ℤ) = (Int.gcd a b : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_negative (a := a) (b := b))
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.GcdNegative
