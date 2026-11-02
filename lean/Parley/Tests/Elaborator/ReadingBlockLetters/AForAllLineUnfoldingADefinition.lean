module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineUnfoldingADefinition

theorem a_for_all_line_unfolding_a_definition (hH1 : ∀ x : ℝ, x ^ 2 ≥ 0) :
    (∀ y : ℝ, abs (y ^ 2) = y ^ 2) := by
  -- 1. proof
  have s1 : ∀ y : ℝ, abs (y ^ 2) = y ^ 2 := by
    intro y
    -- 1.1. def:abs x := y², from H1
    have s1_1 : abs (y ^ 2) = y ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := y ^ 2)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := y ^ 2)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := y ^ 2)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := y ^ 2)) (by parley_side)).symm
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineUnfoldingADefinition
