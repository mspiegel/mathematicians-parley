module

public import Tactics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Algebraic.Defs

/-! Written from tests/elaborator/polynomials-with-integer-coefficients.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PolynomialsWithIntegerCoefficients.ATranscendentalNumber

theorem a_transcendental_number (α : ℝ) (hH2 : Transcendental ℤ (α : ℂ)) :
    Transcendental ℤ (α : ℂ) := by
  -- 1. restate H2
  have s1 : Transcendental ℤ (α : ℂ) := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.PolynomialsWithIntegerCoefficients.ATranscendentalNumber
