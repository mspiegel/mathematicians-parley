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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AnIntegralOfADifference

theorem an_integral_of_a_difference (c : ℝ) (d : ℝ) (hH3 : c < d) (h : ℝ → ℝ) (hH4 : Set.MapsTo h (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (k : ℝ → ℝ) (hH5 : Set.MapsTo k (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (H : ℝ → ℝ) (hH6 : Set.MapsTo H (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (hH7 : ∀ y ∈ (Set.Icc c d : Set ℝ), H y = h y - k y) (hH8 : ContinuousOn h (Set.Icc c d : Set ℝ)) (hH9 : ContinuousOn k (Set.Icc c d : Set ℝ)) :
    (∫ s in c..d, (H s : ℝ)) = (∫ s in c..d, (h s : ℝ)) - (∫ s in c..d, (k s : ℝ)) := by
  -- 1. thm:integral-difference a := c, b := d, f := h, g := k, h := H, from H3, H7, H8, H9
  exact (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := h) (g := k) (h := H) (a := c) (b := d) hH3 hH7 hH8 hH9)

end Parley.Tests.Stdlib.Calculus.AnIntegralOfADifference
