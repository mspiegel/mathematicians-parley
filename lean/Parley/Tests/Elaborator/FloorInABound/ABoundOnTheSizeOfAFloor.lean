module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/floor-in-a-bound.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FloorInABound.ABoundOnTheSizeOfAFloor

theorem a_bound_on_the_size_of_a_floor (A : ℝ) (hH2 : abs ⌊A⌋ = ⌊A⌋) (hH3 : ⌊A⌋ ≤ 1) :
    abs ⌊A⌋ ≤ 1 := by
  -- 1. mun:floor-integer x := A
  -- 2. membership, from 1
  -- 3. transitivity, from H2, H3
  parley_order

end Parley.Tests.Elaborator.FloorInABound.ABoundOnTheSizeOfAFloor
