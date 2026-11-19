module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Written from tests/elaborator/chains.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Chains.DistancesEqual

theorem distances_equal (Q : ℂ) (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (hH6 : dist Q A = dist Q B ∧ dist Q B = dist Q C ∧ dist Q C = dist Q D) (hH7 : dist Q A > 1) :
    dist Q B + dist Q D = 2 * dist Q A ∧ dist Q D > 1 := by
  -- 1. algebra, from H6
  have s1 : dist Q B + dist Q D = 2 * dist Q A := by linear_combination (-2) * hH6.1 + (-1) * hH6.2.1 + (-1) * hH6.2.2
  -- 2. substitute |QA| = |QD| (H6) into H7
  have s2 : dist Q D > 1 := Eq.subst (motive := (fun t : ℝ => t > 1)) (Eq.trans (Eq.trans (hH6.1) hH6.2.1) hH6.2.2) hH7
  -- 3. join 1, 2
  have s3a : dist Q B + dist Q D = 2 * dist Q A := s1
  have s3b : dist Q D > 1 := s2
  exact ⟨s3a, s3b⟩

end Parley.Tests.Elaborator.Chains.DistancesEqual
