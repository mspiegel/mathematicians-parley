module

public import Geometry
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.Equilateral

theorem equilateral (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : LeanBridges.Geometry.Triangle P Q R) (hH5 : dist P Q = dist Q R) (hH6 : dist Q R = dist R P) :
    (LeanBridges.Geometry.Triangle P Q R ∧ dist P Q = dist Q R ∧ dist Q R = dist R P) := by
  -- 1. def:geometry-equilateral, from H4, H5, H6
  exact ((Parley.Items.Stdlib.Geometry.def_equilateral (P := P) (Q := Q) (R := R))).mpr ⟨⟨hH4, hH5⟩, hH6⟩

end Parley.Tests.Stdlib.Geometry.Equilateral
