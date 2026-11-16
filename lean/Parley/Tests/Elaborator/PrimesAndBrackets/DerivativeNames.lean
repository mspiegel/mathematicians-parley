module

public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/elaborator/primes-and-brackets.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PrimesAndBrackets.DerivativeNames

theorem derivative_names (a : ℝ) (b : ℝ) (f : ℝ → ℝ) (hH3 : Set.MapsTo f (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ)) (hH4 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ f x) (hH5 : ContinuousOn (deriv f) (Set.Ioo a b : Set ℝ)) (hH6 : ∀ x ∈ (Set.Ioo a b : Set ℝ), {y : ℝ | (Set.Icc a b : Set ℝ) ∈ nhds y ∧ DifferentiableAt ℝ f y} ∈ nhds x ∧ DifferentiableAt ℝ (deriv f) x) (x : ℝ) (hH7 : x ∈ (Set.Ioo a b : Set ℝ)) (hH8 : (deriv (deriv f)) x = 0) :
    True := by
  -- 1. mun:derivative-real, from H4, H7
  exact trivial

end Parley.Tests.Elaborator.PrimesAndBrackets.DerivativeNames
