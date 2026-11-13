module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-product-from-a-to-b-cited-over-a-set.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AProductFromAToBCitedOverASet.AProductFromAToBCitedOverASet

theorem a_product_from_a_to_b_cited_over_a_set (n : ℤ) :
    True := by
  -- 1. mun:range-finite
  have s1 : (Set.Icc (2 : ℤ) n : Set ℤ).Finite := by exact (Parley.Items.Stdlib.Sums.mun_range_finite (a := (2 : ℤ)) (b := n))
  -- 2. mun:range-in-integers
  have s2 : (Set.Icc (2 : ℤ) n : Set ℤ) ⊆ (Set.univ : Set ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_range_in_integers (a := (2 : ℤ)) (b := n))
  -- 3. mun:product-integer, from 1, 2
  exact trivial

end Parley.Tests.Elaborator.AProductFromAToBCitedOverASet.AProductFromAToBCitedOverASet
