module

public import Tactics
public import Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne

/-! Written from tests/elaborator/citing-a-theorem-over-a-header-recursion.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOneAgain

theorem counted_to_one_again (F : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ ∀ n : ℤ, 0 ≤ n → F (n + 1) = F n + 1) :
    F 1 = 1 := by
  -- 1. thm:counted-to-one
  have s1 : F 1 = 1 := by first | linear_combination (norm := parley_norm) (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne.counted_to_one (F := F) (by parley_side)) | (have h := (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne.counted_to_one (F := F) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne.counted_to_one (F := F) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne.counted_to_one (F := F) (by parley_side)) | exact_mod_cast ((Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne.counted_to_one (F := F) (by parley_side))).symm | (have h := (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne.counted_to_one (F := F) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne.counted_to_one (F := F) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne.counted_to_one (F := F) (by parley_side)); parley_int_power h) | (have h := (Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOne.counted_to_one (F := F) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.CitingATheoremOverAHeaderRecursion.CountedToOneAgain
