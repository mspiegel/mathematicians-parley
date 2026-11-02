module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/requires-in-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RequiresInABlock.AMethodRequiresLineInADirection

theorem a_method_requires_line_in_a_direction (A : ℝ) (B : ℝ) (hH3 : 0 ≤ A) (hH4 : 0 ≤ B) :
    (A < B ↔ A ^ 2 < B ^ 2) := by
  -- 1. both directions
  have s1 : A < B ↔ A ^ 2 < B ^ 2 := by
    constructor
    · skip
      intro hD1
      -- 1.1. mun:square-less x := A, y := B, from D1
      have r17_1 : A ≥ 0 := by parley_side
      have r17_2 : B ≥ 0 := by parley_side
      have s1_1 : A ^ 2 < B ^ 2 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_square_less (x := A) (y := B) (by parley_side) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := A) (y := B) (by parley_side) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_less (x := A) (y := B) (by parley_side) (by parley_side))).mp (by parley_side)
      all_goals parley_side
    · skip
      intro hD2
      -- 1.2. mun:square-less x := A, y := B, from D2
      have r25_1 : A ≥ 0 := by parley_side
      have r25_2 : B ≥ 0 := by parley_side
      have s1_2 : A < B := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := A) (y := B) (by parley_side) (by parley_side))).mpr (by parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.RequiresInABlock.AMethodRequiresLineInADirection
