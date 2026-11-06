module

public import Tactics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Parley.Items.Stdlib.Polynomials

/-! Written from tests/stdlib/polynomials.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Polynomials.ANumberNotAlgebraicIsTranscendental

theorem a_number_not_algebraic_is_transcendental (β : ℂ) (hH2 : ¬ IsAlgebraic ℤ β) :
    Transcendental ℤ β := by
  -- 1. def:transcendental α := β, from H2
  have s1 : Transcendental ℤ β := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Polynomials.def_transcendental (α := β))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Polynomials.def_transcendental (α := β))).mpr (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Polynomials.ANumberNotAlgebraicIsTranscendental
