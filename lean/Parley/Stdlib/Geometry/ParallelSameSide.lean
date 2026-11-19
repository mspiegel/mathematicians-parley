module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Reasoning
public import Parley.Stdlib.Geometry.ParallelOff

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.ParallelSameSide

theorem parallel_same_side (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (X : ℂ) (hH6 : A ≠ B) (hH7 : C ≠ D) (hH8 : Complex.im ((B - A) / (D - C)) = 0) (hH9 : ¬ A ∈ LeanBridges.Geometry.line C D) (hH10 : X ∈ LeanBridges.Geometry.line A B) (hH11 : X ≠ A) :
    0 < Complex.im ((X - C) / (D - C)) * Complex.im ((A - C) / (D - C)) := by
  -- 1. mun:parallel-off, from H6, H7, H8, H9, H10
  have s1 : ¬ X ∈ LeanBridges.Geometry.line C D := by exact (Parley.Stdlib.Geometry.ParallelOff.parallel_off (A := A) (B := B) (C := C) (D := D) (X := X) hH6 hH7 hH8 hH9 hH10)
  -- 2. axi:plane-separation A := C, B := D, P := X, Q := A, from H7, H9, 1
  have s2 : 0 < Complex.im ((X - C) / (D - C)) * Complex.im ((A - C) / (D - C)) ∨ Complex.im ((X - C) / (D - C)) * Complex.im ((A - C) / (D - C)) < 0 := by exact (Parley.Items.Stdlib.Geometry.axi_plane_separation (A := C) (B := D) (P := X) (Q := A) hH7 s1 hH9)
  -- 3. mun:on-line-ends, from H6
  have s3 : A ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := B) hH6)
  -- 4. axi:line-uniqueness B := X, C := A, D := B, from H6, H10, H11, 3
  have s4 : LeanBridges.Geometry.line A X = LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := A) (B := X) (C := A) (D := B) (Ne.symm hH11) hH6 s3 hH10)
  -- 5. contradiction
  have s5 : ¬ Complex.im ((X - C) / (D - C)) * Complex.im ((A - C) / (D - C)) < 0 := by
    intro hS1
    -- 5.1. obtain Y: axi:plane-separation-crossing A := C, B := D, P := X, Q := A, from H7, S1
    obtain ⟨Y, s5_1a, ⟨s5_1b, s5_1c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_plane_separation_crossing (A := C) (B := D) (P := X) (Q := A) hH7 hS1)
    -- 5.2. mun:between-collinear R := Y, S := X, T := A, from 5.1
    have s5_2 : Collinear ℝ {A, Y, X} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := Y) (S := X) (T := A) s5_1c)
    -- 5.3. def:on-line P := Y, B := X, from H11, 5.2
    have s5_3 : Y ∈ LeanBridges.Geometry.line A X := ((Parley.Items.Stdlib.Geometry.def_on_line (A := A) (B := X) (P := Y) (Ne.symm hH11))).mpr (by (have h := s5_2; rw [LeanBridges.Geometry.collinear_swap_23 A Y X] at h; exact h) : Collinear ℝ {A, X, Y})
    -- 5.4. substitute line AX = line AB (line 4) into line 5.3
    have s5_4 : Y ∈ LeanBridges.Geometry.line A B := Eq.subst (motive := (fun t : Set ℂ => Y ∈ t)) s4 s5_3
    -- 5.5. mun:parallel-off X := Y, from H6, H7, H8, H9, 5.4
    have s5_5 : ¬ Y ∈ LeanBridges.Geometry.line C D := by exact (Parley.Stdlib.Geometry.ParallelOff.parallel_off (A := A) (B := B) (C := C) (D := D) (X := Y) hH6 hH7 hH8 hH9 s5_4)
    exact s5_5 s5_1b
  -- 6. mun:disjunctive-syllogism, from 2, 5
  exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism (P := 0 < Complex.im ((X - C) / (D - C)) * Complex.im ((A - C) / (D - C))) (Q := Complex.im ((X - C) / (D - C)) * Complex.im ((A - C) / (D - C)) < 0) s2 s5)

end Parley.Stdlib.Geometry.ParallelSameSide
