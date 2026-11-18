module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.SProd
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Counting

/-! Written from tests/elaborator/products-of-two-types.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ProductsOfTwoTypes.AProductOfTwoNumberTypesCounted

theorem a_product_of_two_number_types_counted (X : Set ℤ) (hH1 : X ⊆ (Set.univ : Set ℤ)) (Y : Set ℚ) (hH2 : Y ⊆ (Set.univ : Set ℚ)) (hH3 : X.Finite) (hH4 : Y.Finite) :
    ((X ×ˢ Y).ncard : ℤ) = (X.ncard : ℤ) * (Y.ncard : ℤ) := by
  -- 1. mun:card-product, from H3, H4
  exact (Parley.Items.Stdlib.Counting.mun_card_product (X := X) (Y := Y) hH3 hH4)

end Parley.Tests.Elaborator.ProductsOfTwoTypes.AProductOfTwoNumberTypesCounted
