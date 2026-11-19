module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-naming-let-with-a-requires-line.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANamingLetWithARequiresLine.ANamingLetWithARequiresLine

theorem a_naming_let_with_a_requires_line (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : A ≠ B) (hH5 : C ≠ B) (hH6 : A ≠ C) :
    (Real.sqrt (Real.sqrt (dist A B)) ^ 2 ≥ 0 ∧ Real.cos (EuclideanGeometry.angle A B C) ^ 2 ≥ 0) := by
  set r : ℝ := Real.sqrt (Real.sqrt (dist A B)) with hD1
  -- 1. mun:square-nonneg
  have s1 : r ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := r))
  -- 2. calculation
  have s2 : Real.sqrt (Real.sqrt (dist A B)) ^ 2 ≥ 0 := by
    calc Real.sqrt (Real.sqrt (dist A B)) ^ 2 = r ^ 2 := by simp (disch := omega) only [hD1]
      _ ≥ 0 := s1
  -- 3. mun:square-nonneg x := cos(∠ABC)
  have s3 : Real.cos (EuclideanGeometry.angle A B C) ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := Real.cos (EuclideanGeometry.angle A B C)))
  -- 4. join 2, 3
  have s4 : Real.sqrt (Real.sqrt (dist A B)) ^ 2 ≥ 0 ∧ Real.cos (EuclideanGeometry.angle A B C) ^ 2 ≥ 0 := ⟨s2, s3⟩
  exact ⟨(s4).1, (s4).2⟩

end Parley.Tests.Elaborator.ANamingLetWithARequiresLine.ANamingLetWithARequiresLine
