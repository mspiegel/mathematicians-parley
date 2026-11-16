module

public import ZF
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
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.Unions

theorem unions {α : Type*} [LeanBridges.ZF.Sets α] (F : Set (Set α)) (hH2 : LeanBridges.ZF.IsSet F) :
    LeanBridges.ZF.IsSet (⋃ A ∈ F, A) := by
  -- 1. axi:sets-unions C := F, from H2
  exact (Parley.Items.Stdlib.Sets.axi_unions (C := F) hH2)

end Parley.Tests.Stdlib.Sets.Unions
