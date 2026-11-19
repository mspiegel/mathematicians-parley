module

public import Polynomials
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Polynomials

/-! Written from tests/stdlib/polynomials.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Polynomials.APolynomialAtAFraction

theorem a_polynomial_at_a_fraction (G : ℂ → ℂ) (hH2 : G ∈ LeanBridges.Polynomials.integerPolynomials) (a : ℤ) (b : ℤ) (hH4 : 0 < b) :
    (∃ m : ℤ, (m : ℂ) = (b : ℂ) ^ LeanBridges.Polynomials.degree G * G ((a : ℂ) / (b : ℂ))) := by
  -- 1. thm:integer-polynomial-at-a-fraction F := G, p := a, q := b, from H2
  exact (Parley.Items.Stdlib.Polynomials.thm_integer_polynomial_at_a_fraction (F := G) hH2 (p := a) (q := b) hH4)

end Parley.Tests.Stdlib.Polynomials.APolynomialAtAFraction
