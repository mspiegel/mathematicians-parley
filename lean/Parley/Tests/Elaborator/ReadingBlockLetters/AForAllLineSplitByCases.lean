module

public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineSplitByCases

theorem a_for_all_line_split_by_cases (hH1 : ∀ x : ℝ, x ≥ 0 ∨ x < 0) :
    (∀ y : ℝ, abs y ≥ 0) := by
  -- 1. proof
  intro y
  -- 1.1. cases, from H1
  rcases (hH1 y) with hC1 | hC2
  · skip
    -- 1.1.1. def:abs x := y, from C1
    have s1_1_1 : abs y = y := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := y)) hC1
    -- 1.1.2. calculation
    calc abs y = y := s1_1_1
      _ ≥ 0 := hC1
  · skip
    -- 1.1.3. def:abs x := y, from C2
    have s1_1_3 : abs y = -y := by exact (Parley.Items.Stdlib.Numbers.def_abs_2 (x := y)) hC2
    -- 1.1.4. inequalities
    have s1_1_4 : -y ≥ 0 := by linarith only [hC2]
    -- 1.1.5. calculation
    calc abs y = -y := s1_1_3
      _ ≥ 0 := s1_1_4

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineSplitByCases
