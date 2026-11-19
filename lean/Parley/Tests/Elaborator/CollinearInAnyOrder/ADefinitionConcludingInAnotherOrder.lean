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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/elaborator/collinear-in-any-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CollinearInAnyOrder.ADefinitionConcludingInAnotherOrder

theorem a_definition_concluding_in_another_order (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) :
    ¬ Collinear ℝ {B, C, A} := by
  -- 1. def:triangle P := A, Q := B, R := C, from H4
  exact (by (have h := (((Parley.Items.Stdlib.Geometry.def_triangle (P := A) (Q := B) (R := C))).mp hH4).2; rw [LeanBridges.Geometry.collinear_rot_231 A B C] at h; exact h) : ¬ Collinear ℝ {B, C, A})

end Parley.Tests.Elaborator.CollinearInAnyOrder.ADefinitionConcludingInAnotherOrder
