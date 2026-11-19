module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry

/-! Written from proofs/euclid/heron-formula.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.HeronFormula.HeronFormula

theorem heron_formula (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) :
    ((1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C)))) : ℝ) : ℂ) = (((dist B C : ℂ) + (dist C A : ℂ) + (dist A B : ℂ)) / 2 * (((dist B C : ℂ) + (dist C A : ℂ) + (dist A B : ℂ)) / 2 - (dist B C : ℂ)) * (((dist B C : ℂ) + (dist C A : ℂ) + (dist A B : ℂ)) / 2 - (dist C A : ℂ)) * (((dist B C : ℂ) + (dist C A : ℂ) + (dist A B : ℂ)) / 2 - (dist A B : ℂ))) ^ (1 / 2 : ℂ) := by
  set s : ℝ := (dist B C + dist C A + dist A B) / 2 with hD1
  -- 1. thm:heron P := A, Q := B, R := C, from D1, H4
  have s1 : ((1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C)))) : ℝ) : ℂ) = ((s : ℂ) * ((s : ℂ) - (dist B C : ℂ)) * (((s : ℂ) - (dist A C : ℂ)) * ((s : ℂ) - (dist A B : ℂ)))) ^ (1 / 2 : ℂ) := by
    simp only [hD1] at ⊢
    push_cast at ⊢
    (have h := (Parley.Items.Stdlib.Geometry.thm_heron (P := A) (Q := B) (R := C) (s := (dist B C + dist C A + dist A B) / 2) hH4.2.2.1 hH4.2.1 (by rw [dist_comm C A])); push_cast at h; exact h)
  -- 2. algebra, from D1
  have s2 : s * (s - dist B C) * (s - dist C A) * (s - dist A B) = s * (s - dist B C) * ((s - dist A C) * (s - dist A B)) := by
    rw [dist_comm C A] at hD1
    rw [dist_comm C A]
    exact (by
      simp only [hD1] at ⊢
      ring1)
  -- 3. substitute s·(s − |BC|)·(s − |CA|)·(s − |AB|) = s·(s − |BC|)·((s − |AC|)·(s − |AB|)) (line 2) into line 1
  have s3 : ((1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C)))) : ℝ) : ℂ) = ((s : ℂ) * ((s : ℂ) - (dist B C : ℂ)) * ((s : ℂ) - (dist C A : ℂ)) * ((s : ℂ) - (dist A B : ℂ))) ^ (1 / 2 : ℂ) := by
    have e_w : (s : ℂ) * ((s : ℂ) - (dist B C : ℂ)) * (((s : ℂ) - (dist A C : ℂ)) * ((s : ℂ) - (dist A B : ℂ))) = (s : ℂ) * ((s : ℂ) - (dist B C : ℂ)) * ((s : ℂ) - (dist C A : ℂ)) * ((s : ℂ) - (dist A B : ℂ)) := by have h := congrArg (fun x : ℝ => (x : ℂ)) s2.symm; push_cast at h ⊢; linear_combination h
    exact Eq.subst (motive := (fun t : ℂ => ((1 / 2 * (dist B C * dist A C) * abs (Real.sin (Complex.arg ((A - C) / (B - C)))) : ℝ) : ℂ) = t ^ (1 / 2 : ℂ))) e_w s1
  (have h := s3; rw [hD1] at h; push_cast at h ⊢; exact h)

end Parley.Proofs.Euclid.HeronFormula.HeronFormula
