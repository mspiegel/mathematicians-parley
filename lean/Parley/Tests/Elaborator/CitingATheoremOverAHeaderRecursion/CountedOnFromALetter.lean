module

public import Tactics
public import Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFrom

/-! Written from tests/elaborator/citing-a-theorem-over-a-header-recursion.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFromALetter

theorem counted_on_from_a_letter (N : ℕ) (F : ℤ → ℤ) (hD1 : F 0 = (N : ℤ) ∧ ∀ j : ℤ, 0 ≤ j → F (j + 1) = F j + 1) :
    F 1 = (N : ℤ) + 1 := by
  -- 1. thm:counted-on-from M := N
  have s1 : F 1 = (N : ℤ) + 1 := by first | linear_combination (norm := parley_norm) (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFrom.counted_on_from (M := N) (F := F) (by parley_side)) | (have h := (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFrom.counted_on_from (M := N) (F := F) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFrom.counted_on_from (M := N) (F := F) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFrom.counted_on_from (M := N) (F := F) (by parley_side)) | exact_mod_cast ((Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFrom.counted_on_from (M := N) (F := F) (by parley_side))).symm | (have h := (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFrom.counted_on_from (M := N) (F := F) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFrom.counted_on_from (M := N) (F := F) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFrom.counted_on_from (M := N) (F := F) (by parley_side)); parley_int_power h) | (have h := (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFrom.counted_on_from (M := N) (F := F) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedOnFromALetter
