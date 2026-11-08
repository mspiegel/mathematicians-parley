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
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AreaIsContinuous

theorem area_is_continuous (c : ℝ) (d : ℝ) (hH3 : c < d) (g : ℝ → ℝ) (hH4 : Set.MapsTo g (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (hH5 : ContinuousOn g (Set.Icc c d : Set ℝ)) (H : ℝ → ℝ) (hH6 : Set.MapsTo H (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (hH7 : ∀ y ∈ (Set.Icc c d : Set ℝ), H y = (∫ s in c..y, (g s : ℝ))) :
    ContinuousOn H (Set.Icc c d : Set ℝ) := by
  -- 1. thm:area-function a := c, b := d, f := g, G := H, from H3, H5, H7
  exact (Parley.Items.Stdlib.Calculus.thm_area_function_1 (f := g) (G := H) (a := c) (b := d) hH3 hH5 hH7)

end Parley.Tests.Stdlib.Calculus.AreaIsContinuous
