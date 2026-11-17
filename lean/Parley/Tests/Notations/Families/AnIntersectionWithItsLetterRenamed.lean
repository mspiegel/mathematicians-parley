module

public import Batteries.Util.ExtendedBinder
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.SetNotation
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

/-! Written from tests/notations/families.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Families.AnIntersectionWithItsLetterRenamed

theorem an_intersection_with_its_letter_renamed {α : Type*} [Nonempty α] (D : Set (Set α)) (Z : Set α) (hH3 : ∀ X ∈ D, Z ⊆ X) :
    Z ⊆ (⋂ Y ∈ D, Y) := by
  -- 1. mun:intersection-within, from H3
  exact (Parley.Items.Stdlib.Sets.mun_intersection_within (D := D) (Z := Z) hH3)

end Parley.Tests.Notations.Families.AnIntersectionWithItsLetterRenamed
