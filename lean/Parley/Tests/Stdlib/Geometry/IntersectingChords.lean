module

public import Batteries.Util.ExtendedBinder
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
public import Mathlib.Data.Set.Defs
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
public import Mathlib.Tactic.Set
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Sets
public import Parley.Stdlib.Geometry.IntersectingChords

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.IntersectingChords

theorem intersecting_chords (O : ℂ) (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (P : ℂ) (r : ℝ) (hH8 : A ∈ {X ∈ (Set.univ : Set ℂ) | dist X O = r}) (hH9 : B ∈ {X ∈ (Set.univ : Set ℂ) | dist X O = r}) (hH10 : C ∈ {X ∈ (Set.univ : Set ℂ) | dist X O = r}) (hH11 : D ∈ {X ∈ (Set.univ : Set ℂ) | dist X O = r}) (hH12 : Sbtw ℝ A P B) (hH13 : Sbtw ℝ C P D) :
    dist P A * dist P B = dist P C * dist P D := by
  set ω : Set ℂ := {X ∈ (Set.univ : Set ℂ) | dist X O = r} with hD1
  -- 1. def:set-builder u := A, from D1, H8
  have s1 : dist A O = r := by
    have hI : dist A O = r := by exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun X : ℂ => dist X O = r)) (X := (Set.univ : Set ℂ)) (u := A))).mp hH8).2)
    exact hI
  -- 2. def:set-builder u := B, from D1, H9
  have s2 : dist B O = r := by
    have hI : dist B O = r := by exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun X : ℂ => dist X O = r)) (X := (Set.univ : Set ℂ)) (u := B))).mp hH9).2)
    exact hI
  -- 3. def:set-builder u := C, from D1, H10
  have s3 : dist C O = r := by
    have hI : dist C O = r := by exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun X : ℂ => dist X O = r)) (X := (Set.univ : Set ℂ)) (u := C))).mp hH10).2)
    exact hI
  -- 4. def:set-builder u := D, from D1, H11
  have s4 : dist D O = r := by
    have hI : dist D O = r := by exact ((((Parley.Items.Stdlib.Sets.def_set_builder (P := (fun X : ℂ => dist X O = r)) (X := (Set.univ : Set ℂ)) (u := D))).mp hH11).2)
    exact hI
  -- 5. transitivity, from 1, 2
  have s5 : dist A O = dist B O := by exact Eq.trans s1 s2.symm
  -- 6. transitivity, from 1, 3
  have s6 : dist A O = dist C O := by exact Eq.trans s1 s3.symm
  -- 7. transitivity, from 1, 4
  have s7 : dist A O = dist D O := by exact Eq.trans s1 s4.symm
  -- 8. thm:geometry-intersecting-chords, from H12, H13, 5, 6, 7
  exact (Parley.Stdlib.Geometry.IntersectingChords.intersecting_chords (A := A) (B := B) (C := C) (D := D) (P := P) (O := O) hH12 hH13 s5 s6 s7)

end Parley.Tests.Stdlib.Geometry.IntersectingChords
