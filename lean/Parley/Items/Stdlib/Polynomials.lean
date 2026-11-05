module

public import Polynomials
public import Tactics

/-! Written from corpus/stdlib/polynomials.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Polynomials

theorem thm_remainder (p : ℂ → ℂ) (h1 : p ∈ LeanBridges.Polynomials.polynomials) (a : ℂ) :
    ∃ q : ℂ → ℂ, q ∈ LeanBridges.Polynomials.polynomials ∧ (∀ x : ℂ, p x = (x - a) * q x + p a) :=
  LeanBridges.Polynomials.remainder p h1 a

theorem mun_polynomial_value (p : ℂ → ℂ) (h1 : p ∈ LeanBridges.Polynomials.polynomials) (x : ℂ) :
    True :=
  trivial

theorem def_transcendental (α : ℂ) :
    Transcendental ℤ α ↔ ¬ IsAlgebraic ℤ α :=
  by (aesop)

end Parley.Items.Stdlib.Polynomials
