module

public import Tactics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Parley.Items.Stdlib.Polynomials

/-! Written from tests/stdlib/polynomials.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Polynomials.ATranscendentalNumberIsNotAlgebraic

theorem a_transcendental_number_is_not_algebraic (β : ℝ) (hH2 : Transcendental ℤ (β : ℂ)) :
    ¬ IsAlgebraic ℤ (β : ℂ) := by
  -- 1. def:transcendental α := β, from H2
  have s1 : ¬ IsAlgebraic ℤ (β : ℂ) := by first | exact ((Parley.Items.Stdlib.Polynomials.def_transcendental (α := (β : ℂ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Polynomials.def_transcendental (α := (β : ℂ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Polynomials.def_transcendental (α := (β : ℂ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Polynomials.def_transcendental (α := (β : ℂ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Polynomials.def_transcendental (α := (β : ℂ)))).mp (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Polynomials.ATranscendentalNumberIsNotAlgebraic
