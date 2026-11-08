module

public import Tactics
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Tactic.NormNum.Basic

/-! Written from tests/elaborator/polynomials-with-integer-coefficients.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PolynomialsWithIntegerCoefficients.ATranscendentalNumber

theorem a_transcendental_number (α : ℝ) (hH2 : Transcendental ℤ (α : ℂ)) :
    Transcendental ℤ (α : ℂ) := by
  -- 1. restate H2
  parley_side

end Parley.Tests.Elaborator.PolynomialsWithIntegerCoefficients.ATranscendentalNumber
