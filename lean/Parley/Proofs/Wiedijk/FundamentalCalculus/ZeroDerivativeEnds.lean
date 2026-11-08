module

public import AlgebraTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
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
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
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
  have r26_1 : a ≤ a := by parley_order
  have r26_2 : a ≤ b := by parley_set_side
  have s1 : a ∈ (Set.Icc a b : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := a) (a := a) (b := b))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := a) (a := a) (b := b))).mpr (by parley_set_side); parley_set_side)
  -- 2. def:interval x := b
  have r31_1 : a ≤ b := by parley_set_side
  have r31_2 : b ≤ b := by parley_order
  have s2 : b ∈ (Set.Icc a b : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := b) (a := a) (b := b))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := b) (a := a) (b := b))).mpr (by parley_set_side); parley_set_side)
  -- 3. obtain c: thm:mean-value f := H, from H3, H5, H6
  obtain ⟨c, s3a, s3b⟩ := (Parley.Proofs.Wiedijk.MeanValue.MeanValue.mean_value (a := a) (b := b) hH3 (f := H) (by parley_set_side) hH5 hH6)
  -- 4. calculation
  have s4 : (H b - H a) / (b - a) = 0 := by
    calc (H b - H a) / (b - a) = (deriv H) c := by parley_set_side
      _ = 0 := by first | linear_combination (norm := parley_norm) (hH7 c (by parley_set_side)) | (have h := (hH7 c (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (hH7 c (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (hH7 c (by parley_set_side)) | exact_mod_cast ((hH7 c (by parley_set_side))).symm | (have h := (hH7 c (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (hH7 c (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (hH7 c (by parley_set_side)); parley_int_power h) | (have h := (hH7 c (by parley_set_side)); parley_set_side)
  -- 5. inequalities
  have s5 : b - a > 0 := by parley_order
  -- 6. algebra, from 4
  have r50_1 : b - a ≠ 0 := by parley_set_side
  linear_combination (norm := parley_field) (-a + b) * s4

end Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds
