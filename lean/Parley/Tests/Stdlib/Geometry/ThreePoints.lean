module

public import Geometry
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
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

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.ThreePoints

theorem three_points :
    (∃ P ∈ (Set.univ : Set ℂ), ∃ Q ∈ (Set.univ : Set ℂ), ∃ R ∈ (Set.univ : Set ℂ), LeanBridges.Geometry.Triangle P Q R) := by
  -- 1. axi:geometry-three-points
  exact Parley.Items.Stdlib.Geometry.axi_three_points

end Parley.Tests.Stdlib.Geometry.ThreePoints
