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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/elaborator/a-hypothesis-letter-from-a-triangle.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AHypothesisLetterFromATriangle.AHypothesisLetterFromATriangleInAnotherOrder

theorem a_hypothesis_letter_from_a_triangle_in_another_order (A : ℂ) (B : ℂ) (D : ℂ) (O : ℂ) (hH5 : LeanBridges.Geometry.Triangle A B D) (hH6 : Sbtw ℝ D O A) :
    LeanBridges.Geometry.Triangle B D O := by
  -- 1. mun:triangle-on-side P := B, Q := D, R := A, S := O, from H5, H6
  exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := B) (Q := D) (R := A) (S := O) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_rot_231 A B D] at h; exact h) : LeanBridges.Geometry.Triangle B D A) hH6)

end Parley.Tests.Elaborator.AHypothesisLetterFromATriangle.AHypothesisLetterFromATriangleInAnotherOrder
