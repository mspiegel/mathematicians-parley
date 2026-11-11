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

namespace Parley.Tests.Elaborator.ListedSetsInAnyOrder.FourInAnEquation

theorem four_in_an_equation {α : Type*} (X : Set α) (a : α) (b : α) (c : α) (d : α) (hH6 : ({a, b, c, d} : Set α) ⊆ X) (hH7 : X ⊆ ({a, b, c, d} : Set α)) :
    X = ({d, b, a, c} : Set α) := by
  -- 1. mun:subset-antisymmetric Y := {a, b, c, d}, from H6, H7
  (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := X) (Y := ({a, b, c, d} : Set α)) hH7 hH6); ext x; rw [Set.ext_iff] at h; specialize h x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢; tauto)

end Parley.Tests.Elaborator.ListedSetsInAnyOrder.FourInAnEquation
