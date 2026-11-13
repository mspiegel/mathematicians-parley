module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-product-reindexed-through-a-define.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AProductReindexedThroughADefine.AValueThroughADefine

theorem a_value_through_a_define (X : Set ℤ) (hH1 : X ⊆ (Set.univ : Set ℤ)) (f : ℤ → ℤ) (hH2 : Set.MapsTo f X X) (L : Set ℤ) (hH3 : L ⊆ X) (U : Set ℤ) (hH4 : U ⊆ X) (hH5 : ∀ x ∈ L, f x ∈ U) :
    (∀ x ∈ L, True) := by
  set g : ℤ → ℤ := fun x : ℤ => f x with hD1
  -- 1. mun:function-into, from D1, H5
  have s1 : Set.MapsTo g L U := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := L) (Y := U) hH5)
  -- 2. mun:subset-transitive, from H1, H4
  have s2 : U ⊆ (Set.univ : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := U) (Y := X) (Z := (Set.univ : Set ℤ)) hH4 hH1)
  -- 3. mun:in-subset, from D1, 1, 2
  intro x h_x; (trivial)

end Parley.Tests.Elaborator.AProductReindexedThroughADefine.AValueThroughADefine
