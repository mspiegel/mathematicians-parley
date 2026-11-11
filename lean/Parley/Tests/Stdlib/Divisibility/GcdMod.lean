module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.GcdMod

theorem gcd_mod (a : ℤ) (b : ℤ) (hH2 : 0 < b) :
    (Int.gcd (a % b) b : ℤ) = (Int.gcd a b : ℤ) := by
  -- 1. thm:divisibility-gcd-mod
  exact (Parley.Items.Stdlib.Divisibility.thm_gcd_mod (a := a) (b := b) hH2)

end Parley.Tests.Stdlib.Divisibility.GcdMod
