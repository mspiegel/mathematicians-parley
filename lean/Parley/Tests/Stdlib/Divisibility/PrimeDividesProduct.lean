module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.PrimeDividesProduct

theorem prime_divides_product (p : ℤ) (hH1 : 0 < p) (hH2 : Nat.Prime p.toNat) (m : ℤ) (n : ℤ) :
    (p ∣ m * n ↔ p ∣ m ∨ p ∣ n) := by
  -- 1. thm:divisibility-prime-divides-product, from H2
  exact (Parley.Items.Stdlib.Divisibility.thm_prime_divides_product (p := p) (by parley_side) hH2 (m := m) (n := n))

end Parley.Tests.Stdlib.Divisibility.PrimeDividesProduct
