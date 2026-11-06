module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.TypeStar

/-! Written from proofs/setmm/onto-bijection-one-to-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OntoBijectionOneToOne.OntoBijectionOneToOne

theorem onto_bijection_one_to_one {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (hH4 : F '' (A ∩ A) = B) :
    (Set.MapsTo F A B ∧ Set.InjOn F A) := by
  -- 1. restate H3
  have s1 : Set.MapsTo F A B ∧ Set.InjOn F A := by parley_set_side
  all_goals exact s1

end Parley.Proofs.Setmm.OntoBijectionOneToOne.OntoBijectionOneToOne
