module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.AValueOfALine

theorem a_value_of_a_line (f : ℝ → ℝ) (hD1 : ∀ x : ℝ, f x = 2 * x + 1) :
    f 3 = 7 := by
  -- 1. D1
  have s1 : f 3 = 2 * 3 + 1 := by (try simp only [hD1]); first | done | parley_side
  -- 2. calculation
  calc f 3 = 2 * 3 + 1 := by parley_side
    _ = 7 := by norm_num

end Parley.Tests.Notations.Functions.AValueOfALine
