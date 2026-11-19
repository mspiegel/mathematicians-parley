module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/elaborator/pairs-compared.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PairsCompared.PointsApartByTheirCoordinates

theorem points_apart_by_their_coordinates (A : ℂ) (B : ℂ) (hH3 : A = Complex.mk (1 : ℝ) (1 : ℝ)) (hH4 : B = Complex.mk (2 : ℝ) (3 : ℝ)) :
    A ≠ B := by
  -- 1. arithmetic
  have s1 : (((1 : ℤ), (1 : ℤ)) : ℤ × ℤ) ≠ ((2 : ℤ), (3 : ℤ)) := fun h => (show (1 : ℤ) ≠ 2 by norm_num) (congrArg Prod.fst h)
  -- 2. mun:points-apart-by-coordinates, from H3, H4, 1
  exact ((Parley.Items.Stdlib.Geometry.mun_points_apart_by_coordinates (A := A) (B := B) (a := (1 : ℝ)) (b := (1 : ℝ)) (c := (2 : ℝ)) (d := (3 : ℝ)) hH3 hH4)).mpr (by (have h := s1; revert h; norm_num))

end Parley.Tests.Elaborator.PairsCompared.PointsApartByTheirCoordinates
