module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Proofs.Setmm.ValueOfOnto.ValueOfOnto

/-! Written from proofs/setmm/onto-bijection-reaches-all.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OntoBijectionReachesAll.OntoBijectionReachesAll

theorem onto_bijection_reaches_all {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (hH4 : F '' (A ∩ A) = B) :
    (∀ y ∈ B, ∃ x ∈ A, y = F x) := by
  -- 1. proof
  intro y hK1
  -- 1.1. thm:value-of-onto, from H4, K1
  exact (Parley.Proofs.Setmm.ValueOfOnto.ValueOfOnto.value_of_onto (A := A) (B := B) (F := F) (by parley_set_side) hH4 (y := y) hK1)

end Parley.Proofs.Setmm.OntoBijectionReachesAll.OntoBijectionReachesAll
