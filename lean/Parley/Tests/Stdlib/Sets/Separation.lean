module

public import ZF
public import Batteries.Util.ExtendedBinder
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

namespace Parley.Tests.Stdlib.Sets.Separation

theorem separation {α : Type*} [Nonempty α] [LeanBridges.ZF.Sets α] (A : Set α) (B : Set α) (hB_set : LeanBridges.ZF.IsSet B) (hH2 : LeanBridges.ZF.IsSet A) :
    LeanBridges.ZF.IsSet {x ∈ A | ¬ x ∈ B} := by
  -- 1. axi:sets-separation, from H2
  exact (Parley.Items.Stdlib.Sets.axi_separation (P := (fun x : α => ¬ x ∈ B)) (X := A) hH2)

end Parley.Tests.Stdlib.Sets.Separation
