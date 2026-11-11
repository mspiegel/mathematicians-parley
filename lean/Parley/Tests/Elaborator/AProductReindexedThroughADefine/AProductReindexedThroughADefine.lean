module

public import InstanceTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-product-reindexed-through-a-define.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AProductReindexedThroughADefine.AProductReindexedThroughADefine

theorem a_product_reindexed_through_a_define (X : Set ℤ) (hH1 : X ⊆ (Set.univ : Set ℤ)) (f : ℤ → ℤ) (hH2 : Set.MapsTo f X X) (L : Set ℤ) (hH3 : L ⊆ X) (hH4 : L.Finite) (U : Set ℤ) (hH5 : U ⊆ X) (hH6 : ∀ x ∈ L, f x ∈ U) (hH7 : ∀ s ∈ L, ∀ t ∈ L, f s = f t → s = t) (hH8 : ∀ u ∈ U, ∃ x ∈ L, u = f x) :
    (∏ᶠ x ∈ U, (x : ℤ)) = (∏ᶠ x ∈ L, (f x : ℤ)) := by
  set g : ℤ → ℤ := fun x : ℤ => f x with hD1
  -- 1. mun:function-into, from D1, H6
  have s1 : Set.MapsTo g L U := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := L) (Y := U) (by parley_set_side) hH6)
  -- 2. def:one-to-one, from D1, H7, 1
  have s2 : Set.MapsTo g L U ∧ Set.InjOn g L := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := L) (Y := U) (f := g) (by parley_set_side))).mpr ⟨by parley_set_side, hH7⟩
  -- 3. def:onto, from D1, H8, 1
  have s3 : Set.MapsTo g L U ∧ Set.SurjOn g L U := ((Parley.Items.Stdlib.Functions.def_onto (X := L) (Y := U) (f := g) (by parley_set_side))).mpr ⟨by parley_set_side, hH8⟩
  -- 4. def:one-to-one-onto, from 2, 3
  have s4 : Set.MapsTo g L U ∧ Set.InjOn g L ∧ Set.SurjOn g L U := ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := L) (Y := U) (f := g) (by parley_set_side))).mpr (by parley_set_side)
  -- 5. mun:subset-transitive, from H1, H5
  have s5 : U ⊆ (Set.univ : Set ℤ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := U) (Y := X) (Z := (Set.univ : Set ℤ)) hH5 hH1)
  -- 6. mun:product-reindex, from D1, H4, 4, 5
  have hI : (∏ᶠ z ∈ U, (z : ℤ)) = (∏ᶠ y ∈ L, (g y : ℤ)) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_product_reindex (t := (fun x : ℤ => x)) (Y := L) (Z := U) (g := g) hH4 s4))
  exact hI

end Parley.Tests.Elaborator.AProductReindexedThroughADefine.AProductReindexedThroughADefine
