module

public import Mathlib

/-!
# Polynomials

A page's polynomial is set.mm's: a function from ℂ to ℂ among the
polynomial functions with complex coefficients, `Poly ℂ`, which the page
applies, p(x). Each item is said in Lean as the build writes it.
-/

public section

namespace LeanBridges.Polynomials

/-- The polynomial functions with complex coefficients, set.mm's `Poly ℂ`:
each is a function from ℂ to ℂ that some Mathlib polynomial gives by
evaluation. -/
@[expose] def polynomials : Set (ℂ → ℂ) :=
  {f | ∃ P : Polynomial ℂ, ∀ x, f x = P.eval x}

/-- `thm:stdlib/polynomials/remainder`: dividing by x − a leaves p(a), from
Mathlib's division by the monic x − a. -/
theorem remainder (p : ℂ → ℂ) (h1 : p ∈ LeanBridges.Polynomials.polynomials) (a : ℂ) :
    ∃ q : ℂ → ℂ, q ∈ LeanBridges.Polynomials.polynomials ∧ (∀ x : ℂ, p x = (x - a) * q x + p a) := by
  obtain ⟨P, hP⟩ := h1
  refine ⟨fun x => (P /ₘ (Polynomial.X - Polynomial.C a)).eval x, ⟨_, fun _ => rfl⟩, fun x => ?_⟩
  have h := Polynomial.modByMonic_add_div P (Polynomial.X - Polynomial.C a)
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at h
  rw [hP x, hP a]
  conv_lhs => rw [← h]
  simp [Polynomial.eval_add, Polynomial.eval_mul]
  ring

end LeanBridges.Polynomials
