module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/requires-in-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RequiresInABlock.AMethodRequiresLineInAContradiction

theorem a_method_requires_line_in_a_contradiction (A : ℝ) (B : ℝ) (hH3 : 0 ≤ A) (hH4 : 0 ≤ B) (hH5 : A < B) :
    A ^ 2 < B ^ 2 := by
  -- 1. contradiction
  have s1 : A ^ 2 < B ^ 2 := by
    by_contra hc_hS1
    have hS1 : ¬ A ^ 2 < B ^ 2 := by parley_suppose hc_hS1
    -- 1.1. inequalities, from S1
    have s1_1 : B ^ 2 ≤ A ^ 2 := by parley_order
    -- 1.2. mun:square-less x := A, y := B, from H5
    have r46_1 : A ≥ 0 := by parley_order
    have r46_2 : B ≥ 0 := by parley_side
    have s1_2 : A ^ 2 < B ^ 2 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_square_less (x := A) (y := B) (by parley_side) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := A) (y := B) (by parley_side) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_less (x := A) (y := B) (by parley_side) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := A) (y := B) (by parley_side) (by parley_side))).mp (by parley_side); parley_side)
    -- 1.3. inequalities, from 1.1
    have s1_3 : ¬ A ^ 2 < B ^ 2 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.RequiresInABlock.AMethodRequiresLineInAContradiction
