module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Convex.Between
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
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.BetweenByCoordinates

theorem between_by_coordinates (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (e : ℝ) (f : ℝ) :
    (Sbtw ℝ (Complex.mk a b) (Complex.mk c d) (Complex.mk e f) ↔ (a - c) * (f - d) = (e - c) * (b - d) ∧ (a - c) * (e - c) + (b - d) * (f - d) < 0) := by
  -- 1. mun:geometry-between-by-coordinates
  exact (Parley.Items.Stdlib.Geometry.mun_between_by_coordinates (a := a) (b := b) (c := c) (d := d) (e := e) (f := f))

end Parley.Tests.Stdlib.Geometry.BetweenByCoordinates
