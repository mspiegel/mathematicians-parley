module

public import OrderTactics
public import Tactics
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

/-! Written from proofs/setmm/less-than-an-integer.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LessThanAnInteger.LessThanAnInteger

theorem less_than_an_integer (A : ℝ) (B : ℤ) :
    (A < (B : ℝ) ↔ ⌊A⌋ < B) := by
  -- 1. mun:floor-integer x := A
  -- 2. mun:floor-below x := A
  have s2 : (⌊A⌋ : ℝ) ≤ A := by exact (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A))
  -- 3. mun:floor-above x := A
  have s3 : A < (⌊A⌋ : ℝ) + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A))
  -- 4. both directions
  have s4 : A < (B : ℝ) ↔ ⌊A⌋ < B := by
    constructor
    · skip
      intro hC1
      -- 4.1. transitivity, from 2, C1
      have s4_1 : ⌊A⌋ < B := by parley_order
      all_goals parley_side
    · skip
      intro hC2
      -- 4.2. mun:integer-step m := ⌊A⌋, n := B, from C2, 1
      have s4_2 : ⌊A⌋ + 1 ≤ B := by exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := ⌊A⌋) (n := B) hC2)
      -- 4.3. transitivity, from 3, 4.2
      have s4_3 : A < (B : ℝ) := by parley_order
      all_goals parley_side
  all_goals exact s4

end Parley.Proofs.Setmm.LessThanAnInteger.LessThanAnInteger
