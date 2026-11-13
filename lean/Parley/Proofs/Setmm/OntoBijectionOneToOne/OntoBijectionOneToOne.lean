module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar

/-! Written from proofs/setmm/onto-bijection-one-to-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OntoBijectionOneToOne.OntoBijectionOneToOne

theorem onto_bijection_one_to_one {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (hH4 : F '' (A ∩ A) = B) :
    (Set.MapsTo F A B ∧ Set.InjOn F A) := by
  -- 1. restate H3
  exact hH3

end Parley.Proofs.Setmm.OntoBijectionOneToOne.OntoBijectionOneToOne
