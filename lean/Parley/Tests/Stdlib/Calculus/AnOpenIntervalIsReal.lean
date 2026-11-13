module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AnOpenIntervalIsReal

theorem an_open_interval_is_real (a : ℝ) (b : ℝ) :
    (Set.Ioo a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by
  -- 1. mun:open-interval-real
  exact (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b))

end Parley.Tests.Stdlib.Calculus.AnOpenIntervalIsReal
