module

public import Geometry
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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.OnLineCases

theorem on_line_cases (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : Q ≠ R) (hH5 : P ∈ LeanBridges.Geometry.line Q R) :
    ((((P = Q ∨ Sbtw ℝ Q P R) ∨ P = R) ∨ Sbtw ℝ Q R P) ∨ Sbtw ℝ P Q R) := by
  -- 1. mun:geometry-on-line-cases, from H4, H5
  exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := P) (Q := Q) (R := R) hH4 hH5)

end Parley.Tests.Stdlib.Geometry.OnLineCases
