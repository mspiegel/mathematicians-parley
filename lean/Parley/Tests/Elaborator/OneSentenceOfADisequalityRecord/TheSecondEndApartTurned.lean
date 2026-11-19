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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/elaborator/one-sentence-of-a-disequality-record.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.OneSentenceOfADisequalityRecord.TheSecondEndApartTurned

theorem the_second_end_apart_turned (R : ℂ) (S : ℂ) (T : ℂ) (hH4 : Sbtw ℝ S R T) :
    R ≠ T := by
  -- 1. mun:between-apart, from H4
  exact Ne.symm (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := R) (S := T) (T := S) (by (have h := hH4; rw [sbtw_comm (x := S) (y := R) (z := T)] at h; exact h) : Sbtw ℝ T R S))

end Parley.Tests.Elaborator.OneSentenceOfADisequalityRecord.TheSecondEndApartTurned
