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
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/pairs-compared.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PairsCompared.PairsEqualByAlgebra

theorem pairs_equal_by_algebra (a : ℝ) (b : ℝ) :
    ((a + b, a * b) : ℝ × ℝ) = (b + a, b * a) := by
  -- 1. algebra
  exact Prod.ext (show a + b = b + a by ring1) (show a * b = b * a by ring1)

end Parley.Tests.Elaborator.PairsCompared.PairsEqualByAlgebra
