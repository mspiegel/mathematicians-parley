module

public import Tactics

/-! Written from tests/elaborator/a-theorem-over-a-define-with-a-square.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut

theorem a_define_with_a_square_written_out (n : ℕ) :
    (∫ t in 0..1, (t ^ n / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (t ^ n / (1 + t ^ 2) : ℝ)) := by
  -- 1. D1
  have s1 : (∫ t in 0..1, (t ^ n / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (t ^ n / (1 + t ^ 2) : ℝ)) := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut
