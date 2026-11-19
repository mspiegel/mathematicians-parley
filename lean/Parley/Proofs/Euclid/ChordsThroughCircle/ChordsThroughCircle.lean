module

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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Stdlib.Geometry.IntersectingChords

/-! Written from proofs/euclid/chords-through-circle.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.ChordsThroughCircle.ChordsThroughCircle

theorem chords_through_circle (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (P : ℂ) (Q : ℂ) (hH7 : dist Q A = dist Q B ∧ dist Q B = dist Q C ∧ dist Q C = dist Q D) (hH8 : Sbtw ℝ A P B) (hH9 : Sbtw ℝ C P D) :
    dist P A * dist P B = dist P C * dist P D := by
  -- 1. thm:intersecting-chords O := Q, from H7, H8, H9
  exact (Parley.Stdlib.Geometry.IntersectingChords.intersecting_chords (A := A) (B := B) (C := C) (D := D) (P := P) (O := Q) hH8 hH9 (by (have h := hH7.1; rw [dist_comm Q A, dist_comm Q B] at h; exact h) : dist A Q = dist B Q) (by (have h := Eq.trans (hH7.1) hH7.2.1; rw [dist_comm Q A, dist_comm Q C] at h; exact h) : dist A Q = dist C Q) (by (have h := Eq.trans (Eq.trans (hH7.1) hH7.2.1) hH7.2.2; rw [dist_comm Q A, dist_comm Q D] at h; exact h) : dist A Q = dist D Q))

end Parley.Proofs.Euclid.ChordsThroughCircle.ChordsThroughCircle
