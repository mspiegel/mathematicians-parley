module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Tests.Elaborator.APhraseDefined

/-! Written from tests/elaborator/a-phrase-defined.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseDefined.SixIsTriangular

theorem six_is_triangular :
    ((0 : ℤ) < 6 ∧ (∃ k : ℤ, 0 < k ∧ 6 = (k : ℚ) * ((k : ℚ) + 1) / 2)) := by
  -- 1. arithmetic
  have s1 : (6 : ℚ) = 3 * (3 + 1) / 2 := by parley_arith
  -- 2. exhibit, from 1
  have s2 : ∃ k : ℤ, 0 < k ∧ 6 = (k : ℚ) * ((k : ℚ) + 1) / 2 := ⟨(3 : ℤ), by parley_side, by parley_side⟩
  -- 3. D1 n := 6, from 2
  have s3 : (0 : ℤ) < 6 ∧ (∃ k : ℤ, 0 < k ∧ 6 = (k : ℚ) * ((k : ℚ) + 1) / 2) := by parley_side
  all_goals exact s3

end Parley.Tests.Elaborator.APhraseDefined.SixIsTriangular
