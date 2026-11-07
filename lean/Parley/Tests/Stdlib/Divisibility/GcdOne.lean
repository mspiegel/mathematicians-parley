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

namespace Parley.Tests.Stdlib.Divisibility.GcdOne

theorem gcd_one (a : ℤ) :
    (Int.gcd a (1 : ℤ) : ℤ) = 1 := by
  -- 1. mun:divisibility-gcd-one
  have s1 : (Int.gcd a (1 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_one (a := a))
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.GcdOne
