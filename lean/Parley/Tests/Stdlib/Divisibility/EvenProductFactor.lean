module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.EvenProductFactor

theorem even_product_factor (a : ℤ) (b : ℤ) :
    (Even (a * b) ↔ Even a ∨ Even b) := by
  -- 1. mun:divisibility-even-product-factor
  exact (Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))

end Parley.Tests.Stdlib.Divisibility.EvenProductFactor
