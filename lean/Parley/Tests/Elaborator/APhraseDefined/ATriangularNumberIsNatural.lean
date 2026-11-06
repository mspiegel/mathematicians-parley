module

public import Tactics
public import Parley.Items.Tests.Elaborator.APhraseDefined

/-! Written from tests/elaborator/a-phrase-defined.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseDefined.ATriangularNumberIsNatural

theorem a_triangular_number_is_natural (x : ℝ) (hH2 : (∃ m : ℤ, 0 < m ∧ (m : ℝ) = x) ∧ (∃ k : ℤ, 0 < k ∧ x = (k : ℝ) * ((k : ℝ) + 1) / 2)) :
    (∃ m : ℤ, 0 < m ∧ (m : ℝ) = x) := by
  -- 1. D1 n := x, from H2
  have s1 : (∃ m : ℤ, 0 < m ∧ (m : ℝ) = x) ∧ (∃ k : ℤ, 0 < k ∧ x = (k : ℝ) * ((k : ℝ) + 1) / 2) := by parley_side
  -- 2. restate 1
  have s2 : ∃ m : ℤ, 0 < m ∧ (m : ℝ) = x := by parley_side
  all_goals exact s2

end Parley.Tests.Elaborator.APhraseDefined.ATriangularNumberIsNatural
