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

namespace Parley.Tests.Stdlib.Divisibility.EvenProduct

theorem even_product (a : ℤ) (hH2 : Even a) (x : ℤ) :
    Even (a * x) := by
  -- 1. mun:divisibility-even-product, from H2
  exact (Parley.Items.Stdlib.Divisibility.mun_even_product (a := a) hH2 (x := x))

end Parley.Tests.Stdlib.Divisibility.EvenProduct
