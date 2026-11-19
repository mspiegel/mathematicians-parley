module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
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
public import Parley.Stdlib.Geometry.HeightArea
public import Parley.Stdlib.Geometry.OffLineAlong

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.SameHeight

theorem same_height (P : ℂ) (Q : ℂ) (R : ℂ) (S : ℂ) (H : ℂ) (T : ℂ) (hH7 : LeanBridges.Geometry.Triangle P Q R) (hH8 : S ∈ LeanBridges.Geometry.line Q R) (hH9 : S ≠ Q) (hH10 : H ∈ LeanBridges.Geometry.line Q R) (hH11 : T ∈ LeanBridges.Geometry.line Q R) (hH12 : T ≠ H) (hH13 : P ≠ H) (hH14 : P ≠ T) (hH15 : EuclideanGeometry.angle P H T = (90 : ℝ) * Real.pi / 180) :
    1 / 2 * (dist Q S * dist P S) * abs (Real.sin (Complex.arg ((P - S) / (Q - S)))) = 1 / 2 * dist Q S * dist P H := by
  -- 1. mun:on-line-ends A := Q, B := R, from H7
  have s1 : Q ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := Q) (B := R) hH7.2.1)
  -- 2. axi:line-uniqueness A := Q, B := S, C := Q, D := R, from H7, H8, H9, 1
  have s2 : LeanBridges.Geometry.line Q S = LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := Q) (B := S) (C := Q) (D := R) (Ne.symm hH9) hH7.2.1 s1 hH8)
  -- 3. substitute line QS = line QR (line 2) into H10
  have s3 : H ∈ LeanBridges.Geometry.line Q S := Eq.subst (motive := (fun t : Set ℂ => H ∈ t)) s2.symm hH10
  -- 4. substitute line QS = line QR (line 2) into H11
  have s4 : T ∈ LeanBridges.Geometry.line Q S := Eq.subst (motive := (fun t : Set ℂ => T ∈ t)) s2.symm hH11
  -- 5. mun:triangle-not-on-line, from H7
  have s5 : ¬ P ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := P) (Q := Q) (R := R) hH7)
  -- 6. mun:off-line-along A := Q, B := R, X := S, from H7, H8, H9, 5
  have s6 : ¬ P ∈ LeanBridges.Geometry.line Q S := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := Q) (B := R) (X := S) (P := P) hH7.2.1 hH8 hH9 s5)
  -- 7. mun:triangle-off-line R := S, from H9, 6
  have s7 : LeanBridges.Geometry.Triangle P Q S := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := P) (Q := Q) (R := S) (Ne.symm hH9) s6)
  -- 8. mun:height-area R := S, S := T, from H12, H13, H14, H15, 3, 4, 7
  exact (Parley.Stdlib.Geometry.HeightArea.height_area (P := P) (Q := Q) (R := S) (H := H) (S := T) s7 s3 s4 hH12 hH13 hH14 hH15)

end Parley.Stdlib.Geometry.SameHeight
