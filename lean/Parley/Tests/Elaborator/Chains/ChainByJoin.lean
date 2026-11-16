module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
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

/-! Written from tests/elaborator/chains.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Chains.ChainByJoin

theorem chain_by_join (x : ℝ) (y : ℝ) (z : ℝ) (w : ℝ) (hH5 : x = y) (hH6 : y = z) (hH7 : z = w) :
    (x = y ∧ y = z ∧ z = w) := by
  -- 1. join H5, H6, H7
  exact ⟨hH5, hH6, hH7⟩

end Parley.Tests.Elaborator.Chains.ChainByJoin
