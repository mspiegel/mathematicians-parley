module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry
public import Parley.Items.Stdlib.Reasoning

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.ParallelOff

theorem parallel_off (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (X : ℂ) (hH6 : A ≠ B) (hH7 : C ≠ D) (hH8 : Complex.im ((B - A) / (D - C)) = 0) (hH9 : ¬ A ∈ LeanBridges.Geometry.line C D) (hH10 : X ∈ LeanBridges.Geometry.line A B) :
    ¬ X ∈ LeanBridges.Geometry.line C D := by
  -- 1. def:parallel, from H6, H7, H8
  have s1 : LeanBridges.Geometry.line A B = LeanBridges.Geometry.line C D ∨ ¬ (∃ Y ∈ (Set.univ : Set ℂ), Y ∈ LeanBridges.Geometry.line A B ∧ Y ∈ LeanBridges.Geometry.line C D) := by exact ((Parley.Items.Stdlib.Geometry.def_parallel (A := A) (B := B) (C := C) (D := D) hH6 hH7)).mp hH8
  -- 2. mun:on-line-ends, from H6
  have s2 : A ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := B) hH6)
  -- 3. contradiction
  have s3 : ¬ LeanBridges.Geometry.line A B = LeanBridges.Geometry.line C D := by
    intro hS1
    -- 3.1. substitute line AB = line CD (S1) into line 2
    have s3_1 : A ∈ LeanBridges.Geometry.line C D := Eq.subst (motive := (fun t : Set ℂ => A ∈ t)) hS1 s2
    exact hH9 s3_1
  -- 4. mun:disjunctive-syllogism-left, from 1, 3
  have s4 : ¬ (∃ Y ∈ (Set.univ : Set ℂ), Y ∈ LeanBridges.Geometry.line A B ∧ Y ∈ LeanBridges.Geometry.line C D) := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := LeanBridges.Geometry.line A B = LeanBridges.Geometry.line C D) (Q := ¬ (∃ Y ∈ (Set.univ : Set ℂ), Y ∈ LeanBridges.Geometry.line A B ∧ Y ∈ LeanBridges.Geometry.line C D)) s1 s3)
  -- 5. contradiction
  intro hS2
  -- 5.1. exhibit, from H10, S2
  have s5_1 : ∃ Y ∈ (Set.univ : Set ℂ), Y ∈ LeanBridges.Geometry.line A B ∧ Y ∈ LeanBridges.Geometry.line C D := ⟨X, Set.mem_univ _, ⟨hH10, hS2⟩⟩
  exact s4 s5_1

end Parley.Stdlib.Geometry.ParallelOff
