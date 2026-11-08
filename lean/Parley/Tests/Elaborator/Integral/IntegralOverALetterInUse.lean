module

public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/integral.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Integral.IntegralOverALetterInUse

theorem integral_over_a_letter_in_use (a : ℝ) (b : ℝ) (x : ℝ) :
    (∫ x in a..b, (x : ℝ)) = (∫ t in a..b, (t : ℝ)) := by
  set J : ℝ := ∫ x in a..b, (x : ℝ) with hD1
  -- 1. D1
  first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side

end Parley.Tests.Elaborator.Integral.IntegralOverALetterInUse
