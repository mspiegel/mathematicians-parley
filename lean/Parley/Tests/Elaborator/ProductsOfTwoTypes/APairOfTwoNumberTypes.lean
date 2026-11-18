module

public import Mathlib.Basic.SProd
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/products-of-two-types.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ProductsOfTwoTypes.APairOfTwoNumberTypes

theorem a_pair_of_two_number_types (n : ℤ) (q : ℚ) :
    (n, q) ∈ (Set.univ : Set ℤ) ×ˢ (Set.univ : Set ℚ) := by
  -- 1. mun:pair-in-product
  exact ((Parley.Items.Stdlib.Sets.mun_pair_in_product (X := (Set.univ : Set ℤ)) (Y := (Set.univ : Set ℚ)) (a := n) (b := q))).mpr ⟨Set.mem_univ _, Set.mem_univ _⟩

end Parley.Tests.Elaborator.ProductsOfTwoTypes.APairOfTwoNumberTypes
