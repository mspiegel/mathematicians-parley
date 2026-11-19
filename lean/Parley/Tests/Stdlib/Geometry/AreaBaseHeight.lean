module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.AreaBaseHeight

theorem area_base_height (P : ℂ) (Q : ℂ) (R : ℂ) (H : ℂ) (hH5 : LeanBridges.Geometry.Triangle P Q R) (hH6 : H ∈ LeanBridges.Geometry.line Q R) (hH7 : P ≠ H ∧ Q ≠ R ∧ Complex.re ((R - Q) / (H - P)) = 0) :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) = 1 / 2 * dist Q R * dist P H := by
  -- 1. axi:geometry-area-base-height, from H5, H6, H7
  exact (Parley.Items.Stdlib.Geometry.axi_area_base_height (H := H) (P := P) (Q := Q) (R := R) hH5 hH6 hH7)

end Parley.Tests.Stdlib.Geometry.AreaBaseHeight
