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

namespace Parley.Tests.Stdlib.Divisibility.GcdCommutes

theorem gcd_commutes (a : ℤ) (b : ℤ) :
    (Int.gcd a b : ℤ) = (Int.gcd b a : ℤ) := by
  -- 1. mun:divisibility-gcd-commutes
  have s1 : (Int.gcd a b : ℤ) = (Int.gcd b a : ℤ) := by exact (Parley.Items.Stdlib.Divisibility.mun_gcd_commutes (a := a) (b := b))
  all_goals exact s1

end Parley.Tests.Stdlib.Divisibility.GcdCommutes
