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

namespace Parley.Tests.Stdlib.Sets.PowerSets

theorem power_sets {α : Type*} [LeanBridges.ZF.Sets α] (A : Set α) (hH2 : LeanBridges.ZF.IsSet A) :
    LeanBridges.ZF.IsSet (𝒫 A) := by
  -- 1. axi:sets-power-sets X := A, from H2
  exact (Parley.Items.Stdlib.Sets.axi_power_sets (X := A) hH2)

end Parley.Tests.Stdlib.Sets.PowerSets
