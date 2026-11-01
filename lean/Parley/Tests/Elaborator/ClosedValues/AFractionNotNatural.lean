module

public import Parley.Library

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.AFractionNotNatural

theorem a_fraction_not_natural :
    ¬ (∃ m : ℕ, 0 < m ∧ (m : ℚ) = 1 / 76) := by
  -- 1. arithmetic
  have s1 : ¬ (∃ m : ℕ, 0 < m ∧ (m : ℚ) = 1 / 76) := by norm_num
  parley_side

end Parley.Tests.Elaborator.ClosedValues.AFractionNotNatural
