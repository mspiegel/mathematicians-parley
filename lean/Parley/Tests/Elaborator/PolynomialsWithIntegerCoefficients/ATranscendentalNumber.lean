module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/polynomials-with-integer-coefficients.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PolynomialsWithIntegerCoefficients.ATranscendentalNumber

theorem a_transcendental_number (α : ℝ) (hH2 : Transcendental ℤ (α : ℂ)) :
    Transcendental ℤ (α : ℂ) := by
  -- 1. restate H2
  exact hH2

end Parley.Tests.Elaborator.PolynomialsWithIntegerCoefficients.ATranscendentalNumber
