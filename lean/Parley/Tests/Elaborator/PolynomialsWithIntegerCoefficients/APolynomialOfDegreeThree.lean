module

public import Polynomials
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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/polynomials-with-integer-coefficients.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PolynomialsWithIntegerCoefficients.APolynomialOfDegreeThree

theorem a_polynomial_of_degree_three (F : ℂ → ℂ) (hH2 : F ∈ LeanBridges.Polynomials.integerPolynomials) (hH3 : (LeanBridges.Polynomials.degree F : ℤ) = 3) :
    (LeanBridges.Polynomials.degree F : ℤ) = 3 := by
  -- 1. restate H3
  exact hH3

end Parley.Tests.Elaborator.PolynomialsWithIntegerCoefficients.APolynomialOfDegreeThree
