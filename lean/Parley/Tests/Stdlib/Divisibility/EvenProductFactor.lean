module

public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.EvenProductFactor

theorem even_product_factor (a : ℤ) (b : ℤ) :
    (Even (a * b) ↔ Even a ∨ Even b) := by
  -- 1. mun:divisibility-even-product-factor
  exact (Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))

end Parley.Tests.Stdlib.Divisibility.EvenProductFactor
