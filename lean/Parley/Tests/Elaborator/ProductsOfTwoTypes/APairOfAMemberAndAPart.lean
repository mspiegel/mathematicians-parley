module

public import Mathlib.Basic.SProd
public import Mathlib.Data.Int.ModEq
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
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/products-of-two-types.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ProductsOfTwoTypes.APairOfAMemberAndAPart

theorem a_pair_of_a_member_and_a_part {α : Type*} [Nonempty α] (X : Set α) (a : α) (B : Set α) (hH4 : a ∈ X) (hH5 : B ⊆ X) :
    (a, B) ∈ X ×ˢ 𝒫 X := by
  -- 1. def:powerset S := B, A := X, from H5
  have s1 : B ∈ 𝒫 X := ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := B))).mpr hH5
  -- 2. mun:pair-in-product, from H4, 1
  exact ((Parley.Items.Stdlib.Sets.mun_pair_in_product (X := X) (Y := 𝒫 X) (a := a) (b := B))).mpr ⟨hH4, s1⟩

end Parley.Tests.Elaborator.ProductsOfTwoTypes.APairOfAMemberAndAPart
