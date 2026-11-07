module

public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductOfReals

theorem a_product_of_reals (n : ℤ) (hH2 : n ≥ 1) (t : ℤ → ℝ) :
    (∏ k ∈ Finset.Icc (1 : ℤ) (n + 1), (t k : ℝ)) = (∏ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ)) * t (n + 1) := by
  -- 1. mun:product-extended a := 1, from H2
  have s1 : (∏ k ∈ Finset.Icc (1 : ℤ) (n + 1), (t k : ℝ)) = (∏ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ)) * t (n + 1) := by exact (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := n) (by parley_side))
  all_goals exact s1

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductOfReals
