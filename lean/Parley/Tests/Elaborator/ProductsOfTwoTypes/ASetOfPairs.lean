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

namespace Parley.Tests.Elaborator.ProductsOfTwoTypes.ASetOfPairs

theorem a_set_of_pairs {α β : Type*} [Nonempty α] [Nonempty β] (X : Set α) (Y : Set β) (S : Set (α × β)) (a : α) (b : β) (hH6 : S ⊆ X ×ˢ Y) (hH7 : (a, b) ∈ S) :
    (a ∈ X ∧ b ∈ Y) := by
  -- 1. mun:in-subset, from H6, H7
  have s1 : (a, b) ∈ X ×ˢ Y := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := S) (Y := X ×ˢ Y) (u := (a, b)) hH6 hH7)
  -- 2. mun:pair-in-product, from 1
  have s2 : a ∈ X ∧ b ∈ Y := by exact ((Parley.Items.Stdlib.Sets.mun_pair_in_product (X := X) (Y := Y) (a := a) (b := b))).mp s1
  exact ⟨(s2).1, (s2).2⟩

end Parley.Tests.Elaborator.ProductsOfTwoTypes.ASetOfPairs
