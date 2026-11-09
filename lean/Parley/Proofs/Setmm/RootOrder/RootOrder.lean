module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/root-order.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RootOrder.RootOrder

theorem root_order (A : ℝ) (B : ℝ) (hH3 : 0 ≤ A) (hH4 : 0 ≤ B) :
    (A < B ↔ Real.sqrt A < Real.sqrt B) := by
  -- 1. def:sqrt x := A, from H3
  have s1a : Real.sqrt A ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A) hH3)
  have s1b : Real.sqrt A ^ 2 = A := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A) hH3)
  -- 2. def:sqrt x := B, from H4
  have s2a : Real.sqrt B ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := B) hH4)
  have s2b : Real.sqrt B ^ 2 = B := by exact (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := B) hH4)
  -- 3. both directions
  constructor
  · skip
    intro hD1
    -- 3.1. transitivity, from 1, D1, 2
    have s3_1 : Real.sqrt A ^ 2 < Real.sqrt B ^ 2 := by parley_order
    -- 3.2. mun:square-less x := √A, y := √B, from 3.1
    have r28_3 : Real.sqrt A ≥ 0 := by parley_side
    have r28_4 : Real.sqrt B ≥ 0 := by parley_side
    exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt A) (y := Real.sqrt B) (by parley_side) (by parley_side))).mpr s3_1
  · skip
    intro hD2
    -- 3.3. mun:square-less x := √A, y := √B, from D2
    have r38_3 : Real.sqrt A ≥ 0 := by parley_side
    have r38_4 : Real.sqrt B ≥ 0 := by parley_side
    have s3_3 : Real.sqrt A ^ 2 < Real.sqrt B ^ 2 := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt A) (y := Real.sqrt B) (by parley_side) (by parley_side))).mp hD2
    -- 3.4. transitivity, from 1, 3.3, 2
    parley_order

end Parley.Proofs.Setmm.RootOrder.RootOrder
