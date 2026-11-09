module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorBasics.TwiceFloorOfHalf

theorem twice_floor_of_half (N : ℤ) :
    N ≤ 2 * ⌊((N : ℝ) + 1) / 2⌋ := by
  set M : ℤ := ⌊((N : ℝ) + 1) / 2⌋ with hD1
  have hD1_kind : True := by trivial
  -- 1. mun:floor-above x := (N + 1)/2, from D1
  have s1 : ((N : ℝ) + 1) / 2 < (M : ℝ) + 1 := by
    try simp only [hD1] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Numbers.mun_floor_above (x := ((N : ℝ) + 1) / 2))
  -- 2. inequalities
  have s2 : N < 2 * M + 1 := by parley_order
  -- 3. mun:integer-step m := N, n := 2M + 1, from 2
  have s3 : N + 1 ≤ 2 * M + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := N) (n := 2 * M + 1) s2)
  -- 4. inequalities, from D1, 3
  parley_order

end Parley.Proofs.Setmm.FloorBasics.TwiceFloorOfHalf
