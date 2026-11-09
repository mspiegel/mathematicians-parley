module

public import InstanceTactics
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
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut

/-! Written from tests/elaborator/a-theorem-over-a-define-with-a-square.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ATheoremOverADefineWithASquare

theorem a_theorem_over_a_define_with_a_square :
    (∫ t in 0..1, (t ^ 0 / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (t ^ 0 / (1 + t ^ 2) : ℝ)) := by
  -- 1. thm:a-define-with-a-square-written-out n := 0
  have hI : (∫ t in 0..1, (t ^ 0 / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (t ^ 0 / (1 + t ^ 2) : ℝ)) := by parley_instance ((Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ADefineWithASquareWrittenOut.a_define_with_a_square_written_out (n := (0 : ℤ)) (by parley_side)))
  exact hI

end Parley.Tests.Elaborator.ATheoremOverADefineWithASquare.ATheoremOverADefineWithASquare
