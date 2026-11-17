module

public import ZF
public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.SetNotation
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
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.Choice

theorem choice {α : Type*} [Nonempty α] [LeanBridges.ZF.Sets α] (F : Set (Set α)) (hH2 : LeanBridges.ZF.IsSet F) (hH3 : ∀ A ∈ F, ¬ A = ∅) :
    (∃ g : Set α → α, Set.MapsTo g F (⋃ B ∈ F, B) ∧ (∀ A ∈ F, g A ∈ A)) := by
  -- 1. obtain g: axi:sets-choice C := F, from H2, H3
  obtain ⟨g, s1a, s1b⟩ := (Parley.Items.Stdlib.Sets.axi_choice (C := F) hH2 hH3)
  -- 2. exhibit, from 1
  exact ⟨g, s1a, s1b⟩

end Parley.Tests.Stdlib.Sets.Choice
