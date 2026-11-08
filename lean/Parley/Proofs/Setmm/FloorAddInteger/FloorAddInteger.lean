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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/floor-add-integer.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FloorAddInteger.FloorAddInteger

theorem floor_add_integer (A : ℝ) (N : ℤ) :
    ⌊A + (N : ℝ)⌋ = ⌊A⌋ + N := by
  -- 1. mun:floor-integer x := A
  -- 2. mun:floor-below x := A
  have s2 : (⌊A⌋ : ℝ) ≤ A := by exact (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A))
  -- 3. mun:floor-above x := A
  have s3 : A < (⌊A⌋ : ℝ) + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A))
  -- 4. inequalities
  have s4 : (⌊A⌋ : ℝ) + (N : ℝ) ≤ A + (N : ℝ) := by parley_order
  -- 5. inequalities
  have s5 : A + (N : ℝ) < (⌊A⌋ : ℝ) + (N : ℝ) + 1 := by parley_order
  -- 6. mun:floor-between x := A + N, k := ⌊A⌋ + N, from 4, 5
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := A + (N : ℝ)) (k := ⌊A⌋ + N))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := A + (N : ℝ)) (k := ⌊A⌋ + N))).mpr (by parley_side); parley_side)

end Parley.Proofs.Setmm.FloorAddInteger.FloorAddInteger
