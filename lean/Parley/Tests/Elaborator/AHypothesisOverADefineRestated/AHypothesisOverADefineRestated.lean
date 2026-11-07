module

public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-hypothesis-over-a-define-restated.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AHypothesisOverADefineRestated.AHypothesisOverADefineRestated

theorem a_hypothesis_over_a_define_restated (n : ℤ) (hH1 : 0 ≤ n) (hH2 : (∫ t in 0..1, (t ^ n.toNat / (1 + t ^ 2) : ℝ)) = 0) :
    (∫ t in 0..1, (t ^ n.toNat / (1 + t ^ 2) : ℝ)) = 0 := by
  -- 1. restate H2
  have s1 : (∫ t in 0..1, (t ^ n.toNat / (1 + t ^ 2) : ℝ)) = 0 := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.AHypothesisOverADefineRestated.AHypothesisOverADefineRestated
