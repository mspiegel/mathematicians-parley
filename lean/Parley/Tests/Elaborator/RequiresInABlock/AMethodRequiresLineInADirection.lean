module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/requires-in-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RequiresInABlock.AMethodRequiresLineInADirection

theorem a_method_requires_line_in_a_direction (A : ℝ) (B : ℝ) (hH3 : 0 ≤ A) (hH4 : 0 ≤ B) :
    (A < B ↔ A ^ 2 < B ^ 2) := by
  -- 1. both directions
  constructor
  · skip
    intro hD1
    -- 1.1. mun:square-less x := A, y := B, from D1
    have r17_1 : A ≥ 0 := by parley_order
    have r17_2 : B ≥ 0 := by parley_side
    exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := A) (y := B) (by parley_side) (by parley_side))).mp hD1
  · skip
    intro hD2
    -- 1.2. mun:square-less x := A, y := B, from D2
    have r25_1 : A ≥ 0 := by parley_side
    have r25_2 : B ≥ 0 := by parley_side
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := A) (y := B) (by parley_side) (by parley_side))).mpr hD2 | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := A) (y := B) (by parley_side) (by parley_side))).mpr hD2; parley_side)

end Parley.Tests.Elaborator.RequiresInABlock.AMethodRequiresLineInADirection
