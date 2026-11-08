module

public import Tactics
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Polynomials

/-! Written from tests/stdlib/polynomials.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Polynomials.ATranscendentalNumberIsNotAlgebraic

theorem a_transcendental_number_is_not_algebraic (β : ℝ) (hH2 : Transcendental ℤ (β : ℂ)) :
    ¬ IsAlgebraic ℤ (β : ℂ) := by
  -- 1. def:transcendental α := β, from H2
  exact ((Parley.Items.Stdlib.Polynomials.def_transcendental (α := (β : ℂ)))).mp hH2

end Parley.Tests.Stdlib.Polynomials.ATranscendentalNumberIsNotAlgebraic
