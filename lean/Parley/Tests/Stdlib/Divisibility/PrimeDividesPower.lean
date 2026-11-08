module

public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.PrimeDividesPower

theorem prime_divides_power (q : ℤ) (hH1 : 0 < q) (hH2 : Nat.Prime q.toNat) (x : ℤ) (k : ℤ) (hH4 : 0 < k) :
    (q ∣ x ^ k.toNat ↔ q ∣ x) := by
  -- 1. thm:divisibility-prime-divides-power p := q, a := x, n := k, from H2
  exact (Parley.Items.Stdlib.Divisibility.thm_prime_divides_power (p := q) (by parley_side) hH2 (a := x) (n := k) (by parley_side))

end Parley.Tests.Stdlib.Divisibility.PrimeDividesPower
