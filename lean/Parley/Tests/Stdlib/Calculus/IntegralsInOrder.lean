module

public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.IntegralsInOrder

theorem integrals_in_order (c : ℝ) (d : ℝ) (hH3 : c < d) (h : ℝ → ℝ) (hH4 : Set.MapsTo h (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (k : ℝ → ℝ) (hH5 : Set.MapsTo k (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (hH6 : ∀ y ∈ (Set.Icc c d : Set ℝ), h y ≤ k y) (hH7 : ContinuousOn h (Set.Icc c d : Set ℝ)) (hH8 : ContinuousOn k (Set.Icc c d : Set ℝ)) :
    (∫ s in c..d, (h s : ℝ)) ≤ (∫ s in c..d, (k s : ℝ)) := by
  -- 1. thm:integral-order a := c, b := d, f := h, g := k, from H3, H6, H7, H8
  exact (Parley.Items.Stdlib.Calculus.thm_integral_order (f := h) (g := k) (a := c) (b := d) hH3 hH6 hH7 hH8)

end Parley.Tests.Stdlib.Calculus.IntegralsInOrder
