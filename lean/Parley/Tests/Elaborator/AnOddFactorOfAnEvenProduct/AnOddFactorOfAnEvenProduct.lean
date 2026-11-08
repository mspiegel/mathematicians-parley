module

public import Tactics
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/an-odd-factor-of-an-even-product.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnOddFactorOfAnEvenProduct.AnOddFactorOfAnEvenProduct

theorem an_odd_factor_of_an_even_product (a : ℤ) (b : ℤ) (hH3 : Odd a) (hH4 : Even (a * b)) :
    Even b := by
  -- 1. mun:even-product-factor, from H4
  have s1 : Even a ∨ Even b := ((Parley.Items.Stdlib.Divisibility.mun_even_product_factor (a := a) (b := b))).mp hH4
  -- 2. mun:odd-not-even, from H3
  have s2 : ¬ Even a := by exact (Parley.Items.Stdlib.Divisibility.mun_odd_not_even (n := a) hH3)
  -- 3. mun:disjunctive-syllogism-left, from 1, 2
  exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := Even a) (Q := Even b) s1 s2)

end Parley.Tests.Elaborator.AnOddFactorOfAnEvenProduct.AnOddFactorOfAnEvenProduct
