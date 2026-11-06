module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/listed-sets-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.ATripleInAnEquation

theorem a_triple_in_an_equation {α : Type*} (X : Set α) (a : α) (b : α) (c : α) (hH5 : ({a, b, c} : Set α) ⊆ X) (hH6 : X ⊆ ({a, b, c} : Set α)) :
    ({b, c, a} : Set α) = X := by
  -- 1. mun:subset-antisymmetric X := {a, b, c}, Y := X, from H5, H6
  have s1 : ({b, c, a} : Set α) = X := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := ({a, b, c} : Set α)) (Y := X) hH5 hH6) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := ({a, b, c} : Set α)) (Y := X) hH5 hH6)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := ({a, b, c} : Set α)) (Y := X) hH5 hH6) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := ({a, b, c} : Set α)) (Y := X) hH5 hH6) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := ({a, b, c} : Set α)) (Y := X) hH5 hH6); ext x; rw [Set.ext_iff] at h; specialize h x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢; tauto) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := ({a, b, c} : Set α)) (Y := X) hH5 hH6); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.ATripleInAnEquation
