module

public import ZF
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
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

namespace Parley.Tests.Stdlib.Sets.Replacement

theorem replacement {α : Type*} [LeanBridges.ZF.Sets α] (A : Set α) (B : Set α) (hB_set : LeanBridges.ZF.IsSet B) (hH2 : LeanBridges.ZF.IsSet A) (g : α → α) (hH4 : Set.MapsTo g A B) :
    LeanBridges.ZF.IsSet ((fun x : α => g x) '' A) := by
  -- 1. axi:sets-replacement Y := A, Z := B, E := g, from H2
  exact (Parley.Items.Stdlib.Sets.axi_replacement (E := g) (Y := A) (Z := B) hB_set hH2 hH4)

end Parley.Tests.Stdlib.Sets.Replacement
