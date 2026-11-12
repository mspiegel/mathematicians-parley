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
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorBasics.IntegerAtMostFloor

theorem integer_at_most_floor (A : ℝ) (B : ℤ) :
    ((B : ℝ) ≤ A ↔ B ≤ ⌊A⌋) := by
  -- 1. mun:floor-integer x := A
  -- 2. mun:floor-below x := A
  have s2 : (⌊A⌋ : ℝ) ≤ A := by exact (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A))
  -- 3. mun:floor-above x := A
  have s3 : A < (⌊A⌋ : ℝ) + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A))
  -- 4. both directions
  constructor
  · skip
    intro hC1
    by_contra hS
    -- 4.1. inequalities, from S
    have s4_1 : ⌊A⌋ < B := by linarith only [hS]
    -- 4.2. mun:integer-step m := ⌊A⌋, n := B, from 1, 4.1
    have s4_2 : ⌊A⌋ + 1 ≤ B := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊A⌋) (n := B) s4_1)
    -- 4.3. transitivity, from 3, 4.2
    have s4_3 : A < (B : ℝ) := by parley_order
    -- 4.4. inequalities, from 4.3
    have s4_4 : ¬ (B : ℝ) ≤ A := by linarith only [s4_3]
    exact s4_4 hC1
  · skip
    intro hC2
    -- 4.5. transitivity, from C2, 2
    parley_order

end Parley.Proofs.Setmm.FloorBasics.IntegerAtMostFloor
