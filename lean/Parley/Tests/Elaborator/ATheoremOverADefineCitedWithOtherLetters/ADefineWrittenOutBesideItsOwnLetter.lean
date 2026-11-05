module

public import Tactics

/-! Written from tests/elaborator/a-theorem-over-a-define-cited-with-other-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter

theorem a_define_written_out_beside_its_own_letter (n : ℕ) :
    (∫ t in 0..1, (t ^ n : ℝ)) = (∫ t in 0..1, (t ^ n : ℝ)) := by
  -- 1. D1
  have s1 : (∫ t in 0..1, (t ^ n : ℝ)) = (∫ t in 0..1, (t ^ n : ℝ)) := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter
