module

public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.Monoid
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
public import Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter

/-! Written from tests/elaborator/a-theorem-over-a-define-cited-with-other-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ATheoremOverADefineCitedWithOtherLetters

theorem a_theorem_over_a_define_cited_with_other_letters :
    (∫ t in 0..1, (t ^ 0 : ℝ)) = (∫ b in 0..1, (b ^ 0 : ℝ)) := by
  -- 1. thm:a-define-written-out-beside-its-own-letter n := 0
  exact (Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ADefineWrittenOutBesideItsOwnLetter.a_define_written_out_beside_its_own_letter (n := (0 : ℤ)) (by parley_side))

end Parley.Tests.Elaborator.ATheoremOverADefineCitedWithOtherLetters.ATheoremOverADefineCitedWithOtherLetters
