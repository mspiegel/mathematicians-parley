module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/docs/tri.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Tri.TriOne

theorem tri_one :
    (1 * (1 + 1) / 2 : ℚ) = 1 := by
  -- 1. calculation
  calc (1 * (1 + 1) / 2 : ℚ) = 1 * (1 + 1) / 2 := rfl
    _ = 1 := by norm_num

end Parley.Tests.Docs.Tri.TriOne
