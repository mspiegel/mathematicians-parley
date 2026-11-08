module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.GcdInteger

theorem gcd_integer (a : ℤ) (b : ℤ) :
    (Int.gcd a b : ℤ) ∣ b := by
  -- 1. mun:divisibility-gcd-integer
  exact (Parley.Items.Stdlib.Divisibility.mun_gcd_integer_3 (a := a) (b := b))

end Parley.Tests.Stdlib.Divisibility.GcdInteger
