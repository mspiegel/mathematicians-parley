module

public import Polynomials
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Polynomials

/-! Written from tests/stdlib/polynomials.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Polynomials.APolynomialRealAtAReal

theorem a_polynomial_real_at_a_real (G : ℂ → ℂ) (hH2 : G ∈ LeanBridges.Polynomials.integerPolynomials) (y : ℝ) :
    (∃ m : ℝ, (m : ℂ) = G (y : ℂ)) := by
  -- 1. mun:integer-polynomial-real F := G, x := y, from H2
  exact (Parley.Items.Stdlib.Polynomials.mun_integer_polynomial_real (F := G) hH2 (x := y))

end Parley.Tests.Stdlib.Polynomials.APolynomialRealAtAReal
