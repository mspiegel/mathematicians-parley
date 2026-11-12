module

public import AlgebraTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Proofs.Wiedijk.MeanValue.MeanValue

/-! Written from proofs/wiedijk/fundamental-calculus.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds

theorem zero_derivative_ends (a : ℝ) (b : ℝ) (hH3 : a < b) (H : ℝ → ℝ) (hH4 : Set.MapsTo H (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ)) (hH5 : ContinuousOn H (Set.Icc a b : Set ℝ)) (hH6 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ H x) (hH7 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv H) x = 0) :
    H b = H a := by
  -- 1. def:interval x := a
  have r26_1 : a ≤ a := by linarith
  have r26_2 : a ≤ b := by linarith only [hH3]
  have s1 : a ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := a) (a := a) (b := b))).mpr ⟨⟨by parley_set_side, r26_1⟩, r26_2⟩
  -- 2. def:interval x := b
  have r31_1 : a ≤ b := by linarith only [hH3]
  have r31_2 : b ≤ b := by linarith
  have s2 : b ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := b) (a := a) (b := b))).mpr ⟨⟨by parley_set_side, r31_1⟩, r31_2⟩
  -- 3. obtain c: thm:mean-value f := H, from H3, H5, H6
  obtain ⟨c, s3a, s3b⟩ := (Parley.Proofs.Wiedijk.MeanValue.MeanValue.mean_value (a := a) (b := b) hH3 (f := H) (by parley_set_side) hH5 hH6)
  -- 4. calculation
  have s4 : (H b - H a) / (b - a) = 0 := by
    calc (H b - H a) / (b - a) = (deriv H) c := by exact s3b.symm
      _ = 0 := by exact (hH7 c s3a)
  -- 5. inequalities
  have s5 : b - a > 0 := by linarith only [hH3]
  -- 6. algebra, from 4
  have r50_1 : b - a ≠ 0 := ne_of_gt (by linarith only [s5])
  linear_combination (norm := parley_field) (-a + b) * s4

end Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds
