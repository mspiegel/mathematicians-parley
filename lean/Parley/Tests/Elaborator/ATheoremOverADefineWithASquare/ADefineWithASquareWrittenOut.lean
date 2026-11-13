module

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
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-theorem-over-a-define-with-a-square.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut

theorem a_define_with_a_square_written_out (n : ℤ) (hH1 : 0 ≤ n) :
    (∫ t in 0..1, (t ^ n.toNat / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (t ^ n.toNat / (1 + t ^ 2) : ℝ)) := by
  -- 1. D1
  exact rfl

end Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut
