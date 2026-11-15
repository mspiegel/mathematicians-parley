module

public import Mathlib.Tactic.Ring
public import Lean.Elab.MutualDef
public import Lean.Parser.Command
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Factorials

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

/-- `def:stdlib/polynomials/B`: the page's recursion for the Bernoulli
polynomials, from Mathlib's `bernoulli_eq_sub_sum`, (n + 1)·Bₙ = (n + 1)·xⁿ −
Σ(k < n) C(n + 1, k)·Bₖ, divided by n + 1, as C(n + 1, k)·(n + 1 − k) =
C(n, k)·(n + 1). -/
theorem B (n : ℤ) (h1 : 0 ≤ n) (x : ℂ) :
    Polynomial.aeval x (Polynomial.bernoulli n.toNat) = x ^ n.toNat - (∑ k ∈ Finset.Icc (0 : ℤ) (n - 1), ((LeanBridges.Counting.choose n k : ℂ) * (Polynomial.aeval x (Polynomial.bernoulli k.toNat) / ((n : ℂ) - (k : ℂ) + 1)) : ℂ)) := by
  lift n to ℕ using h1
  have key := congrArg (Polynomial.aeval x) (Polynomial.bernoulli_eq_sub_sum n)
  simp only [nsmul_eq_mul, map_sub, map_sum, map_mul, map_natCast, map_pow,
    Polynomial.aeval_X] at key
  have hsum : (∑ k ∈ Finset.Icc (0 : ℤ) ((n : ℤ) - 1), ((LeanBridges.Counting.choose n k : ℂ) * (Polynomial.aeval x (Polynomial.bernoulli k.toNat) / (((n : ℤ) : ℂ) - (k : ℂ) + 1)) : ℂ))
      = ∑ k ∈ Finset.range n, (((n + 1).choose k : ℂ) / ((n : ℂ) + 1)) * Polynomial.aeval x (Polynomial.bernoulli k) := by
    refine Finset.sum_nbij' (fun k : ℤ => k.toNat) (fun k : ℕ => (k : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
    · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Int.toNat_of_nonneg hk.1]
    · intro k _; simp
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk.1
      have hm : m < n := by omega
      simp only [LeanBridges.Counting.choose_natCast, Int.toNat_natCast, Int.cast_natCast]
      have hc : ((n + 1).choose m : ℂ) * ((n : ℂ) + 1 - m) = (n.choose m : ℂ) * ((n : ℂ) + 1) := by
        have := Nat.choose_mul_succ_eq n m
        have h' : ((n + 1 - m : ℕ) : ℂ) = (n : ℂ) + 1 - m := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [← h']; exact_mod_cast this.symm
      have hz1 : (n : ℂ) + 1 ≠ 0 := by norm_cast
      have hz2 : (n : ℂ) - (m : ℂ) + 1 ≠ 0 := by
        have : ((n - m + 1 : ℕ) : ℂ) ≠ 0 := by norm_cast
        rw [Nat.cast_add, Nat.cast_sub (by omega)] at this; simpa using this
      rw [mul_div_assoc', div_mul_eq_mul_div, div_eq_div_iff hz2 hz1]
      linear_combination (-(Polynomial.aeval x (Polynomial.bernoulli m))) * hc
  rw [Int.toNat_natCast, hsum]
  have hz1 : (n : ℂ) + 1 ≠ 0 := by norm_cast
  apply mul_left_cancel₀ hz1
  rw [mul_sub, Finset.mul_sum]
  push_cast at key
  rw [key]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

end LeanBridges.Polynomials
