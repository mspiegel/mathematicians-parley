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

namespace Parley.Tests.Elaborator.CollinearInAnyOrder.ACollinearityHeldInAnotherOrder

theorem a_collinearity_held_in_another_order (P : ℂ) (A : ℂ) (B : ℂ) (hH4 : Collinear ℝ {B, P, A}) (hH5 : A ≠ B) :
    P ∈ LeanBridges.Geometry.line A B := by
  -- 1. def:on-line, from H4, H5
  exact ((Parley.Items.Stdlib.Geometry.def_on_line (A := A) (B := B) (P := P) hH5)).mpr (by (have h := hH4; rw [LeanBridges.Geometry.collinear_rot_312 B P A] at h; exact h) : Collinear ℝ {A, B, P})

end Parley.Tests.Elaborator.CollinearInAnyOrder.ACollinearityHeldInAnotherOrder
