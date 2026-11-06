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

theorem mun_bernoulli_complex (n : ℤ) (h1 : 0 ≤ n) (x : ℂ) :
    True :=
  by trivial

theorem thm_bernoulli_difference (n : ℤ) (h1 : 0 < n) (x : ℂ) :
    Polynomial.aeval (x + 1) (Polynomial.bernoulli n.toNat) - Polynomial.aeval x (Polynomial.bernoulli n.toNat) = (n : ℂ) * x ^ (n - 1) :=
  by lift n to ℕ using h1.le; simp only [Int.toNat_natCast]; have h := congr_arg (Polynomial.aeval x) (Polynomial.bernoulli_comp_one_add_X n); simp only [Polynomial.aeval_comp, map_add, nsmul_eq_mul, map_mul, map_natCast, map_pow, Polynomial.aeval_X, map_one] at h; push_cast; rw [add_comm x 1, h, (show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by omega), zpow_natCast]; ring

theorem def_transcendental (α : ℂ) :
    Transcendental ℤ α ↔ ¬ IsAlgebraic ℤ α :=
  by (aesop)

end Parley.Items.Stdlib.Polynomials
