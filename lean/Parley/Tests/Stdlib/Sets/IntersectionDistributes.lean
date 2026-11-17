module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
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
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.IntersectionDistributes

theorem intersection_distributes {α : Type*} [Nonempty α] (X : Set α) (Y : Set α) (Z : Set α) :
    X ∩ (Y ∪ Z) = X ∩ Y ∪ X ∩ Z := by
  -- 1. mun:sets-intersection-distributes
  exact (Parley.Items.Stdlib.Sets.mun_intersection_distributes (X := X) (Y := Y) (Z := Z))

end Parley.Tests.Stdlib.Sets.IntersectionDistributes
