module

public import Parley.Library

/-! Written from tests/elaborator/three-names.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ThreeNames.ThreeNames

theorem three_names (hH1 : ∃ a : ℕ, 0 < a ∧ (∃ b : ℕ, 0 < b ∧ (∃ c : ℕ, 0 < c ∧ (a : ℤ) + 2 * (b : ℤ) + 3 * (c : ℤ) = 6))) :
    (∃ a : ℕ, 0 < a ∧ (∃ b : ℕ, 0 < b ∧ (∃ c : ℕ, 0 < c ∧ 3 * (c : ℤ) + 2 * (b : ℤ) + (a : ℤ) = 6))) := by
  -- 1. obtain a, b, c from H1
  obtain ⟨a, s1a, b, s1b, c, s1c, s1d⟩ := hH1
  -- 2. algebra, from 1
  have s2 : 3 * (c : ℤ) + 2 * (b : ℤ) + (a : ℤ) = 6 := by linear_combination s1d
  -- 3. exhibit, from 2
  have s3 : ∃ a : ℕ, 0 < a ∧ (∃ b : ℕ, 0 < b ∧ (∃ c : ℕ, 0 < c ∧ 3 * (c : ℤ) + 2 * (b : ℤ) + (a : ℤ) = 6)) := ⟨a, by parley_side, b, by parley_side, c, by parley_side, by parley_side⟩
  all_goals parley_side

end Parley.Tests.Elaborator.ThreeNames.ThreeNames
