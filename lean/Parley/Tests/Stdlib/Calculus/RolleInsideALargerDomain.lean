module

public import SetTactics
public import Tactics
public import WholeTactics
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.RolleInsideALargerDomain

theorem rolle_inside_a_larger_domain (a : ℝ) (b : ℝ) (hH3 : a < b) (h : ℝ → ℝ) (hH5 : ContinuousOn h (Set.Icc a b : Set ℝ)) (hH6 : ∀ x ∈ (Set.Ioo a b : Set ℝ), DifferentiableAt ℝ h x) (hH7 : h a = h b) :
    (∃ c ∈ (Set.Ioo a b : Set ℝ), (deriv h) c = 0) := by
  -- 1. mun:interval-real
  have s1 : (Set.Icc a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b))
  -- 2. mun:subset-self X := ℝ
  have s2 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))
  -- 3. thm:rolle-on-part D := ℝ, f := h, from H3, H5, H6, H7, 1, 2
  have s3 : ∃ c ∈ (Set.Ioo a b : Set ℝ), (deriv h) c = 0 := by exact (Parley.Items.Stdlib.Calculus.thm_rolle_on_part (f := h) (D := (Set.univ : Set ℝ)) (by parley_whole_side) (a := a) (b := b) hH3 (by parley_whole_side) hH5 (by parley_whole_side) hH7)
  all_goals exact s3

end Parley.Tests.Stdlib.Calculus.RolleInsideALargerDomain
