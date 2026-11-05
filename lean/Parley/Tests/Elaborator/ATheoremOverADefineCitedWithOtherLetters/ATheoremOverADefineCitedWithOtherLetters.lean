module

public import PowerTactics
public import Tactics
public import Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter

/-! Written from tests/elaborator/a-theorem-over-a-define-cited-with-other-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ATheoremOverADefineCitedWithOtherLetters

theorem a_theorem_over_a_define_cited_with_other_letters :
    (∫ t in 0..1, (t ^ 0 : ℝ)) = (∫ b in 0..1, (b ^ 0 : ℝ)) := by
  -- 1. thm:a-define-written-out-beside-its-own-letter n := 0
  have s1 : (∫ t in 0..1, (t ^ 0 : ℝ)) = (∫ b in 0..1, (b ^ 0 : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter.a_define_written_out_beside_its_own_letter (n := 0)) | (have h := (Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter.a_define_written_out_beside_its_own_letter (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter.a_define_written_out_beside_its_own_letter (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter.a_define_written_out_beside_its_own_letter (n := 0)) | exact_mod_cast ((Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter.a_define_written_out_beside_its_own_letter (n := 0))).symm | (have h := (Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter.a_define_written_out_beside_its_own_letter (n := 0)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter.a_define_written_out_beside_its_own_letter (n := 0)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter.a_define_written_out_beside_its_own_letter (n := 0)); parley_int_power h) | (have h := (Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter.a_define_written_out_beside_its_own_letter (n := 0)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ATheoremOverADefineCitedWithOtherLetters
