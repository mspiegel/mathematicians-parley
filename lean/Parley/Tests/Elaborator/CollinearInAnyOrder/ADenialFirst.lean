module

public import Geometry
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/elaborator/collinear-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CollinearInAnyOrder.ADenialFirst

theorem a_denial_first (A : ℂ) (B : ℂ) (C : ℂ) (M : ℂ) (hH5 : LeanBridges.Geometry.Triangle A B C) (hH6 : Collinear ℝ {C, M, B}) :
    A ≠ M := by
  -- 1. contradiction
  intro hS
  -- 1.1. def:triangle P := A, Q := B, R := C, from H5
  have s1_1 : ¬ Collinear ℝ {A, B, C} := by exact (((Parley.Items.Stdlib.Geometry.def_triangle (P := A) (Q := B) (R := C))).mp hH5).2
  -- 1.2. substitute M = A (S) into H6
  have s1_2 : Collinear ℝ {C, A, B} := Eq.subst (motive := (fun t : ℂ => Collinear ℝ {C, t, B})) hS.symm hH6
  exact s1_1 (by (have h := s1_2; rw [LeanBridges.Geometry.collinear_rot_231 C A B] at h; exact h) : Collinear ℝ {A, B, C})

end Parley.Tests.Elaborator.CollinearInAnyOrder.ADenialFirst
