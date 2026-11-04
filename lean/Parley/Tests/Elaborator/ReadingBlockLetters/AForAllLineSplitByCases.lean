module

public import OrderTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineSplitByCases

theorem a_for_all_line_split_by_cases (hH1 : ∀ x : ℝ, x ≥ 0 ∨ x < 0) :
    (∀ y : ℝ, abs y ≥ 0) := by
  -- 1. proof
  have s1 : ∀ y : ℝ, abs y ≥ 0 := by
    intro y
    -- 1.1. cases, from H1
    have s1_1 : abs y ≥ 0 := by
      rcases (hH1 y) with hC1 | hC2
      · skip
        -- 1.1.1. def:abs x := y, from C1
        have s1_1_1 : abs y = y := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := y)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := y)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := y)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := y)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := y)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := y)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := y)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := y)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := y)) (by parley_side); parley_side)
        -- 1.1.2. calculation
        have s1_1_2 : abs y ≥ 0 := by
          calc abs y = y := by parley_side
            _ ≥ 0 := by parley_side
        all_goals parley_side
      · skip
        -- 1.1.3. def:abs x := y, from C2
        have s1_1_3 : abs y = -y := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_2 (x := y)) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := y)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := y)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_2 (x := y)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_2 (x := y)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := y)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := y)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := y)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := y)) (by parley_side); parley_side)
        -- 1.1.4. inequalities
        have s1_1_4 : -y ≥ 0 := by parley_order
        -- 1.1.5. calculation
        have s1_1_5 : abs y ≥ 0 := by
          calc abs y = -y := by parley_side
            _ ≥ 0 := by parley_side
        all_goals parley_side
    all_goals exact s1_1
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineSplitByCases
