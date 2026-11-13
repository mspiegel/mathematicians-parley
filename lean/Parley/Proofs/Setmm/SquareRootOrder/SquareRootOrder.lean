module

public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/square-root-order.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SquareRootOrder.SquareRootOrder

theorem square_root_order (A : ℝ) (B : ℝ) (hH3 : 0 ≤ A) (hH4 : 0 ≤ B) :
    (A ≤ B ↔ Real.sqrt A ≤ Real.sqrt B) := by
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
    by_contra hS1
    -- 3.1. inequalities, from S1
    have s3_1 : Real.sqrt B < Real.sqrt A := by linarith only [hS1]
    -- 3.2. calculation
    have s3_2 : B < A := by
      calc B = Real.sqrt B ^ 2 := s2b.symm
        _ < Real.sqrt A ^ 2 := by exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt B) (y := Real.sqrt A) s2a s1a)).mp s3_1
        _ = A := s1b
    -- 3.3. inequalities, from 3.2
    have s3_3 : ¬ A ≤ B := by linarith only [s3_2]
    exact s3_3 hD1
  · skip
    intro hD2
    by_contra hS2
    -- 3.4. inequalities, from S2
    have s3_4 : B < A := by linarith only [hS2]
    -- 3.5. calculation
    have s3_5 : Real.sqrt B ^ 2 < Real.sqrt A ^ 2 := by
      calc Real.sqrt B ^ 2 = B := s2b
        _ < A := s3_4
        _ = Real.sqrt A ^ 2 := s1b.symm
    -- 3.6. mun:square-less x := √B, y := √A, from 1, 2, 3.5
    have s3_6 : Real.sqrt B < Real.sqrt A := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := Real.sqrt B) (y := Real.sqrt A) s2a s1a)).mpr s3_5
    -- 3.7. inequalities, from 3.6
    have s3_7 : ¬ Real.sqrt A ≤ Real.sqrt B := by linarith only [s3_6]
    exact s3_7 hD2

end Parley.Proofs.Setmm.SquareRootOrder.SquareRootOrder
