module

public import Mathlib.Algebra.Group.Monoid
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
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Proofs.Wiedijk.Chords.PowerOfAPoint

/-! Written from proofs/wiedijk/chords.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Chords.IntersectingChords

theorem intersecting_chords (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (P : ℂ) (O : ℂ) (hH7 : Sbtw ℝ A P B) (hH8 : Sbtw ℝ C P D) (hH9 : dist A O = dist B O) (hH10 : dist A O = dist C O) (hH11 : dist A O = dist D O) :
    dist P A * dist P B = dist P C * dist P D := by
  -- 1. calculation
  have s1 : dist C O = dist D O := by
    calc dist C O = dist A O := hH10.symm
      _ = dist D O := hH11
  -- 2. thm:power-of-a-point A := C, B := D, from H8, 1
  have s2 : dist P C * dist P D = dist C O ^ 2 - dist P O ^ 2 := by exact (Parley.Proofs.Wiedijk.Chords.PowerOfAPoint.power_of_a_point (A := C) (B := D) (P := P) (O := O) hH8 s1)
  -- 3. substitute |CO| = |AO| (H10) into line 2
  have s3 : dist P C * dist P D = dist A O ^ 2 - dist P O ^ 2 := Eq.subst (motive := (fun t : ℝ => dist P C * dist P D = t ^ 2 - dist P O ^ 2)) hH10.symm s2
  -- 4. calculation
  calc dist P A * dist P B = dist A O ^ 2 - dist P O ^ 2 := by exact (Parley.Proofs.Wiedijk.Chords.PowerOfAPoint.power_of_a_point (A := A) (B := B) (P := P) (O := O) hH7 hH9)
    _ = dist P C * dist P D := s3.symm

end Parley.Proofs.Wiedijk.Chords.IntersectingChords
