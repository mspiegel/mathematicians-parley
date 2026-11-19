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
public import Parley.Stdlib.Geometry.Foot
public import Parley.Stdlib.Geometry.HeightArea
public import Parley.Stdlib.Geometry.ParallelHeights

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.SameBaseArea

theorem same_base_area (Q : ℂ) (R : ℂ) (X : ℂ) (Y : ℂ) (hH5 : Q ≠ R) (hH6 : LeanBridges.Geometry.Triangle Q X Y) (hH7 : LeanBridges.Geometry.Triangle R X Y) (hH8 : Complex.im ((Y - X) / (R - Q)) = 0) :
    1 / 2 * (dist X Y * dist Q Y) * abs (Real.sin (Complex.arg ((Q - Y) / (X - Y)))) = 1 / 2 * (dist X Y * dist R Y) * abs (Real.sin (Complex.arg ((R - Y) / (X - Y)))) := by
  -- 1. obtain H, S: mun:foot P := Q, Q := X, R := Y, from H6
  obtain ⟨H, s1a, S, s1b, ⟨⟨⟨⟨⟨s1c, s1d⟩, s1e⟩, s1f⟩, s1g⟩, s1h⟩⟩ := (Parley.Stdlib.Geometry.Foot.foot (P := Q) (Q := X) (R := Y) hH6)
  -- 2. obtain K, T: mun:foot P := R, Q := X, R := Y, from H7
  obtain ⟨K, s2a, T, s2b, ⟨⟨⟨⟨⟨s2c, s2d⟩, s2e⟩, s2f⟩, s2g⟩, s2h⟩⟩ := (Parley.Stdlib.Geometry.Foot.foot (P := R) (Q := X) (R := Y) hH7)
  -- 3. mun:parallel-turned A := X, B := Y, C := Q, D := R, from H6, H8
  have s3 : Complex.im ((R - Q) / (Y - X)) = 0 := by exact (Parley.Items.Stdlib.Geometry.mun_parallel_turned (A := X) (B := Y) (C := Q) (D := R) hH6.2.1 hH8)
  -- 4. mun:triangle-not-on-line P := Q, Q := X, R := Y, from H6
  have s4 : ¬ Q ∈ LeanBridges.Geometry.line X Y := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := Q) (Q := X) (R := Y) hH6)
  -- 5. thm:parallel-heights, from H5, H6, 1, 2, 3, 4
  have s5 : dist Q H = dist R K := by exact (Parley.Stdlib.Geometry.ParallelHeights.parallel_heights (Q := Q) (R := R) (X := X) (Y := Y) (H := H) (S := S) (K := K) (T := T) hH5 hH6.2.1 s3 s4 s1c s1d s1e s1h s2c s2d s2e s2h s1f s1g s2f s2g)
  -- 6. calculation
  calc 1 / 2 * (dist X Y * dist Q Y) * abs (Real.sin (Complex.arg ((Q - Y) / (X - Y)))) = 1 / 2 * dist X Y * dist Q H := by exact (Parley.Stdlib.Geometry.HeightArea.height_area (P := Q) (Q := X) (R := Y) (H := H) (S := S) hH6 s1c s1d s1e s1f s1g s1h)
    _ = 1 / 2 * dist X Y * dist R K := congrArg (fun t : ℝ => 1 / 2 * dist X Y * t) s5
    _ = 1 / 2 * (dist X Y * dist R Y) * abs (Real.sin (Complex.arg ((R - Y) / (X - Y)))) := by exact (Parley.Stdlib.Geometry.HeightArea.height_area (P := R) (Q := X) (R := Y) (H := K) (S := T) hH7 s2c s2d s2e s2f s2g s2h).symm

end Parley.Stdlib.Geometry.SameBaseArea
