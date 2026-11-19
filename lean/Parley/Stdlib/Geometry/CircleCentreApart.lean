module

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

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.CircleCentreApart

theorem circle_centre_apart (X : ℂ) (Y : ℂ) (O : ℂ) (hH4 : X ≠ Y) (hH5 : dist X O = dist Y O) :
    X ≠ O := by
  -- the theorem. contradiction
  intro hS
  -- 1. mun:distance-zero P := X, Q := O, from S
  have s1 : dist X O = 0 := ((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := X) (Q := O))).mpr hS
  -- 2. substitute |XO| = |YO| (H5) into line 1
  have s2 : dist Y O = 0 := Eq.subst (motive := (fun t : ℝ => t = 0)) hH5 s1
  -- 3. calculation
  have s3 : X = Y := by
    calc X = O := hS
      _ = Y := by exact (((Parley.Items.Stdlib.Geometry.mun_distance_zero (P := Y) (Q := O))).mp s2).symm
  exact hH4 s3

end Parley.Stdlib.Geometry.CircleCentreApart
