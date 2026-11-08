module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/listed-sets-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairFromLines

theorem a_pair_from_lines {α : Type*} (X : Set α) (u : α) (w : α) (hH4 : ({u, w} : Set α) ⊆ X) (hH5 : X ⊆ ({u, w} : Set α)) :
    X = ({w, u} : Set α) := by
  -- 1. mun:subset-antisymmetric Y := {u, w}, from H4, H5
  first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := X) (Y := ({u, w} : Set α)) hH5 hH4) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := X) (Y := ({u, w} : Set α)) hH5 hH4)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := X) (Y := ({u, w} : Set α)) hH5 hH4) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := X) (Y := ({u, w} : Set α)) hH5 hH4) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := X) (Y := ({u, w} : Set α)) hH5 hH4); ext x; rw [Set.ext_iff] at h; specialize h x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢; tauto) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := X) (Y := ({u, w} : Set α)) hH5 hH4); parley_set_side)

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.APairFromLines
