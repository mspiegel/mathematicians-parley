module

public import Parley.Library

/-! Written from tests/elaborator/a-define-filling-a-cited-function.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne

theorem value_at_one (f : ℤ → ℝ) (hH2 : ∀ k : ℕ, 0 < k → f (k : ℤ) = (k : ℝ) + 1) :
    f 1 = 1 + 1 := by
  -- 1. instantiate k := 1 in H2
  have s1 : f 1 = 1 + 1 := by first | linear_combination (norm := parley_norm) (hH2 1 (by parley_side)) | (have h := (hH2 1 (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (hH2 1 (by parley_side)) | exact_mod_cast ((hH2 1 (by parley_side))).symm | (have h := (hH2 1 (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH2 1 (by parley_side)); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Tests.Elaborator.ADefineFillingACitedFunction.ValueAtOne
