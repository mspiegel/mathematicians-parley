module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-basics.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorBasics.FloorOfInteger

theorem floor_of_integer (A : ℤ) :
    ⌊(A : ℝ)⌋ = A := by
  -- 1. inequalities
  have s1 : A ≤ A := by parley_order
  -- 2. inequalities
  have s2 : A < A + 1 := by parley_order
  -- 3. mun:floor-between x := A, k := A, from 1, 2
  have s3 : ⌊(A : ℝ)⌋ = A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℝ)) (k := A))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := (A : ℝ)) (k := A))).mpr (by parley_side); parley_side)
  all_goals exact s3

end Parley.Proofs.Setmm.FloorBasics.FloorOfInteger
