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
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductOfOneFactor

theorem a_product_of_one_factor (t : ℤ → ℝ) :
    (∏ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (t k : ℝ)) = t 1 := by
  -- 1. mun:product-single a := 1
  exact (Parley.Items.Stdlib.Sums.mun_product_single (t := t) (a := (1 : ℤ)))

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductOfOneFactor
