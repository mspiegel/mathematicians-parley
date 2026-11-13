module

public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/docs/tri.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Tri.TriOne

theorem tri_one :
    (1 * (1 + 1) / 2 : ℚ) = 1 := by
  -- 1. calculation
  calc (1 * (1 + 1) / 2 : ℚ) = 1 * (1 + 1) / 2 := rfl
    _ = 1 := by norm_num

end Parley.Tests.Docs.Tri.TriOne
