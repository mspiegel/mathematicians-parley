module

public import PowerTactics
public import Tactics
public import Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut

/-! Written from tests/elaborator/a-theorem-over-a-define-with-a-square.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ATheoremOverADefineWithASquare

theorem a_theorem_over_a_define_with_a_square :
    (∫ t in 0..1, (t ^ 0 / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (t ^ 0 / (1 + t ^ 2) : ℝ)) := by
  -- 1. thm:a-define-with-a-square-written-out n := 0
  have s1 : (∫ t in 0..1, (t ^ 0 / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (t ^ 0 / (1 + t ^ 2) : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut.a_define_with_a_square_written_out (n := (0 : ℤ)) (by parley_side)) | (have h := (Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut.a_define_with_a_square_written_out (n := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut.a_define_with_a_square_written_out (n := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut.a_define_with_a_square_written_out (n := (0 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut.a_define_with_a_square_written_out (n := (0 : ℤ)) (by parley_side))).symm | (have h := (Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut.a_define_with_a_square_written_out (n := (0 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut.a_define_with_a_square_written_out (n := (0 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut.a_define_with_a_square_written_out (n := (0 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut.a_define_with_a_square_written_out (n := (0 : ℤ)) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ATheoremOverADefineWithASquare
