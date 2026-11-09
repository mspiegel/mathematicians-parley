module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/floor-in-a-bound.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FloorInABound.ARoundingErrorAtMostAHalf

theorem a_rounding_error_at_most_a_half (A : ℝ) (hH2 : (⌊A + 1 / 2⌋ : ℝ) - A ≥ 0) (hH3 : (⌊A + 1 / 2⌋ : ℝ) - A ≤ 1 / 2) :
    abs ((⌊A + 1 / 2⌋ : ℝ) - A) ≤ 1 / 2 := by
  -- 1. mun:floor-integer x := A + 1/2
  -- 2. membership, from 1
  -- 3. def:abs x := ⌊A + 1/2⌋ − A, from H2, 2
  have s3 : abs ((⌊A + 1 / 2⌋ : ℝ) - A) = (⌊A + 1 / 2⌋ : ℝ) - A := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := (⌊A + 1 / 2⌋ : ℝ) - A)) hH2
  -- 4. transitivity, from 3, H3
  parley_order

end Parley.Tests.Elaborator.FloorInABound.ARoundingErrorAtMostAHalf
