module

public import Parley.Library

/-! Written from tests/elaborator/divisors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Divisors.TwoEquationsThenDivided

theorem two_equations_then_divided (x : ℝ) (y : ℝ) (z : ℝ) (H4 : y = 1) (H5 : z = 2) (H6 : x + 3 ≠ 0) :
    (x * y + z) / (x + 3) = (x + 2) / (x + 3) := by
  -- 1. algebra, from H4, H5
  have r69_1 : x + 3 ≠ 0 := by parley_side
  have s1 : (x * y + z) / (x + 3) = (x + 2) / (x + 3) := by linear_combination (norm := parley_field) ((x) / ((x + 3))) * H4 + ((1) / ((x + 3))) * H5
  all_goals parley_side

end Parley.Tests.Elaborator.Divisors.TwoEquationsThenDivided
