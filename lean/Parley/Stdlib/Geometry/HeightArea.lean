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

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.HeightArea

theorem height_area (P : ℂ) (Q : ℂ) (R : ℂ) (H : ℂ) (S : ℂ) (hH6 : LeanBridges.Geometry.Triangle P Q R) (hH7 : H ∈ LeanBridges.Geometry.line Q R) (hH8 : S ∈ LeanBridges.Geometry.line Q R) (hH9 : S ≠ H) (hH10 : P ≠ H) (hH11 : P ≠ S) (hH12 : EuclideanGeometry.angle P H S = (90 : ℝ) * Real.pi / 180) :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) = 1 / 2 * dist Q R * dist P H := by
  -- 1. mun:perpendicular-by-right-angle Q := H, R := S, from H9, H10, H11, H12
  have s1 : H ≠ P ∧ H ≠ S ∧ Complex.re ((S - H) / (P - H)) = 0 := ((Parley.Items.Stdlib.Geometry.mun_perpendicular_by_right_angle (P := P) (Q := H) (R := S) hH10 hH9 hH11)).mpr hH12
  -- 2. mun:perpendicular-turned A := H, B := P, C := H, D := S, from 1
  have s2 : P ≠ H ∧ H ≠ S ∧ Complex.re ((S - H) / (H - P)) = 0 := by exact (Parley.Items.Stdlib.Geometry.mun_perpendicular_turned (A := H) (B := P) (C := H) (D := S) s1)
  -- 3. axi:line-uniqueness A := H, B := S, C := Q, D := R, from H6, H7, H8, H9
  have s3 : LeanBridges.Geometry.line H S = LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := H) (B := S) (C := Q) (D := R) (Ne.symm hH9) hH6.2.1 hH7 hH8)
  -- 4. mun:on-line-ends A := Q, B := R, from H6
  have s4a : Q ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := Q) (B := R) hH6.2.1)
  have s4b : R ∈ LeanBridges.Geometry.line Q R := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := Q) (B := R) hH6.2.1)
  -- 5. substitute line HS = line QR (line 3) into line 4
  have s5 : Q ∈ LeanBridges.Geometry.line H S := Eq.subst (motive := (fun t : Set ℂ => Q ∈ t)) s3.symm s4a
  -- 6. substitute line HS = line QR (line 3) into line 4
  have s6 : R ∈ LeanBridges.Geometry.line H S := Eq.subst (motive := (fun t : Set ℂ => R ∈ t)) s3.symm s4b
  -- 7. mun:perpendicular-along A := P, B := H, C := H, D := S, E := Q, F := R, from H6, 2, 5, 6
  have s7 : P ≠ H ∧ Q ≠ R ∧ Complex.re ((R - Q) / (H - P)) = 0 := by exact (Parley.Items.Stdlib.Geometry.mun_perpendicular_along (A := P) (B := H) (C := H) (D := S) (E := Q) (F := R) s2 s5 s6 hH6.2.1)
  -- 8. axi:area-base-height, from H6, H7, 7
  exact (Parley.Items.Stdlib.Geometry.axi_area_base_height (H := H) (P := P) (Q := Q) (R := R) hH6 hH7 s7)

end Parley.Stdlib.Geometry.HeightArea
