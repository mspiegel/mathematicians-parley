module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Parley.Items.Tests.Elaborator.APhraseDefined

/-! Written from tests/elaborator/a-phrase-imported.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseImported.TenIsTriangular

theorem ten_is_triangular :
    ((0 : ℤ) < 10 ∧ (∃ k : ℤ, 0 < k ∧ 10 = (k : ℚ) * ((k : ℚ) + 1) / 2)) := by
  -- 1. arithmetic
  have s1 : (10 : ℚ) = 4 * (4 + 1) / 2 := by parley_arith
  -- 2. exhibit, from 1
  have s2 : ∃ k : ℤ, 0 < k ∧ 10 = (k : ℚ) * ((k : ℚ) + 1) / 2 := ⟨(4 : ℤ), by parley_side, by parley_side⟩
  -- 3. def:triangular-number n := 10, from 2
  have s3 : (0 : ℤ) < 10 ∧ (∃ k : ℤ, 0 < k ∧ 10 = (k : ℚ) * ((k : ℚ) + 1) / 2) := by parley_side
  all_goals exact s3

end Parley.Tests.Elaborator.APhraseImported.TenIsTriangular
