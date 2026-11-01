module

public import Parley.Library

/-! Written from tests/elaborator/divided-equations-combined.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DividedEquationsCombined.TwoDividedEquationsSubtracted

theorem two_divided_equations_subtracted (A : ℝ) (B : ℝ) (p : ℤ) (q : ℕ) (H4 : 0 < q) (r : ℤ) (s : ℕ) (H6 : 0 < s) (H7 : A + B = (p : ℝ) / (q : ℝ)) (H8 : B = (r : ℝ) / (s : ℝ)) :
    A = (p : ℝ) / (q : ℝ) - (r : ℝ) / (s : ℝ) := by
  -- 1. algebra, from H7, H8
  have s1 : A = (p : ℝ) / (q : ℝ) - (r : ℝ) / (s : ℝ) := by linear_combination (norm := parley_field) H7 + (-1) * H8
  parley_side

end Parley.Tests.Elaborator.DividedEquationsCombined.TwoDividedEquationsSubtracted
