module

public import OrderTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-is-monotone.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorIsMonotone.FloorIsMonotone

theorem floor_is_monotone (A : ℝ) (B : ℝ) (hH3 : A ≤ B) :
    ⌊A⌋ ≤ ⌊B⌋ := by
  -- 1. mun:floor-integer x := A
  -- 2. mun:floor-integer x := B
  -- 3. mun:floor-below x := A
  have s3 : (⌊A⌋ : ℝ) ≤ A := by exact (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A))
  -- 4. mun:floor-above x := B
  have s4 : B < (⌊B⌋ : ℝ) + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_floor_above (x := B))
  -- 5. contradiction
  by_contra hS
  -- 5.1. inequalities, from S
  have s5_1 : ⌊B⌋ < ⌊A⌋ := by parley_order
  -- 5.2. mun:integer-step m := ⌊B⌋, n := ⌊A⌋, from 1, 2, 5.1
  have s5_2 : ⌊B⌋ + 1 ≤ ⌊A⌋ := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊B⌋) (n := ⌊A⌋) s5_1)
  -- 5.3. transitivity, from 5.2, 3, H3
  have s5_3 : (⌊B⌋ : ℝ) + 1 ≤ B := by parley_order
  -- 5.4. inequalities, from 5.3
  have s5_4 : ¬ B < (⌊B⌋ : ℝ) + 1 := by parley_side
  exact s5_4 s4

end Parley.Proofs.Setmm.FloorIsMonotone.FloorIsMonotone
