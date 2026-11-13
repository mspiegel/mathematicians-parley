module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
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
public import Parley.Items.Stdlib.Polynomials

/-! Written from tests/stdlib/polynomials.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Polynomials.ANumberNotAlgebraicIsTranscendental

theorem a_number_not_algebraic_is_transcendental (β : ℂ) (hH2 : ¬ IsAlgebraic ℤ β) :
    Transcendental ℤ β := by
  -- 1. def:transcendental α := β, from H2
  exact ((Parley.Items.Stdlib.Polynomials.def_transcendental (α := β))).mpr hH2

end Parley.Tests.Stdlib.Polynomials.ANumberNotAlgebraicIsTranscendental
