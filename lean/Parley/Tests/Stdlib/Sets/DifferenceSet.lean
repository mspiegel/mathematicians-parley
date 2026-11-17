module

public import ZF
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.DifferenceSet

theorem difference_set {α : Type*} [Nonempty α] [LeanBridges.ZF.Sets α] (X : Set α) (hX_set : LeanBridges.ZF.IsSet X) (a : α) (ha_set : LeanBridges.ZF.IsSet a) :
    LeanBridges.ZF.IsSet (X \ ({a} : Set α)) := by
  -- 1. mun:sets-difference-set
  exact (Parley.Items.Stdlib.Sets.mun_difference_set (X := X) hX_set (a := a) ha_set)

end Parley.Tests.Stdlib.Sets.DifferenceSet
