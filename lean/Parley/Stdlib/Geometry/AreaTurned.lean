module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
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
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.Foot
public import Parley.Stdlib.Geometry.HeightArea

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.AreaTurned

theorem area_turned (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : LeanBridges.Geometry.Triangle P Q R) :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) = 1 / 2 * (dist R Q * dist P Q) * abs (Real.sin (Complex.arg ((P - Q) / (R - Q)))) := by
  -- 1. obtain H, S: mun:foot, from H4
  obtain ⟨H, s1a, S, s1b, ⟨⟨⟨⟨⟨s1c, s1d⟩, s1e⟩, s1f⟩, s1g⟩, s1h⟩⟩ := (Parley.Stdlib.Geometry.Foot.foot (P := P) (Q := Q) (R := R) hH4)
  -- 2. def:on-line P := H, A := Q, B := R, from H4, 1
  have s2 : Collinear ℝ {Q, R, H} := by exact ((Parley.Items.Stdlib.Geometry.def_on_line (A := Q) (B := R) (P := H) hH4.2.1)).mp s1c
  -- 3. def:on-line P := H, A := R, B := Q, from H4, 2
  have s3 : H ∈ LeanBridges.Geometry.line R Q := ((Parley.Items.Stdlib.Geometry.def_on_line (A := R) (B := Q) (P := H) (Ne.symm hH4.2.1))).mpr (by (have h := s2; rw [LeanBridges.Geometry.collinear_swap_12 Q R H] at h; exact h) : Collinear ℝ {R, Q, H})
  -- 4. def:on-line P := S, A := Q, B := R, from H4, 1
  have s4 : Collinear ℝ {Q, R, S} := by exact ((Parley.Items.Stdlib.Geometry.def_on_line (A := Q) (B := R) (P := S) hH4.2.1)).mp s1d
  -- 5. def:on-line P := S, A := R, B := Q, from H4, 4
  have s5 : S ∈ LeanBridges.Geometry.line R Q := ((Parley.Items.Stdlib.Geometry.def_on_line (A := R) (B := Q) (P := S) (Ne.symm hH4.2.1))).mpr (by (have h := s4; rw [LeanBridges.Geometry.collinear_swap_12 Q R S] at h; exact h) : Collinear ℝ {R, Q, S})
  -- 6. calculation
  calc 1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) = 1 / 2 * dist Q R * dist P H := by exact (Parley.Stdlib.Geometry.HeightArea.height_area (P := P) (Q := Q) (R := R) (H := H) (S := S) hH4 s1c s1d s1e s1f s1g s1h)
    _ = 1 / 2 * dist R Q * dist P H := by
        rw [dist_comm P H, dist_comm R Q]
    _ = 1 / 2 * (dist R Q * dist P Q) * abs (Real.sin (Complex.arg ((P - Q) / (R - Q)))) := by exact (Parley.Stdlib.Geometry.HeightArea.height_area (P := P) (Q := R) (R := Q) (H := H) (S := S) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 P Q R] at h; exact h) : LeanBridges.Geometry.Triangle P R Q) s3 s5 s1e s1f s1g s1h).symm

end Parley.Stdlib.Geometry.AreaTurned
