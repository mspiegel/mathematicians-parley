module

public import Tactics
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

namespace Parley.Proofs.Setmm.FloorBasics.FloorAtMostOneMore

theorem floor_at_most_one_more (A : ℝ) :
    A ≤ (⌊A⌋ : ℝ) + 1 := by
  -- 1. mun:floor-integer x := A
  -- 2. mun:floor-above x := A
  have s2 : A < (⌊A⌋ : ℝ) + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A))
  -- 3. inequalities
  linarith only [s2]

end Parley.Proofs.Setmm.FloorBasics.FloorAtMostOneMore
