module

public import Mathlib.Tactic.Ring
public import Lean.Elab.MutualDef
public import Lean.Parser.Command
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.LinearAlgebra.Complex.Module
public import Factorials

/-!
# Polynomials

A page's polynomial is set.mm's: a function from ℂ to ℂ among the
polynomial functions with complex coefficients, `Poly ℂ`, which the page
applies, p(x). One with integer coefficients is among set.mm's `Poly ℤ`,
the functions a polynomial over ℤ gives, and its degree is set.mm's `deg`,
of the one polynomial over ℂ that gives it. Each item is said in Lean as
the build writes it.
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

section Integer

open Polynomial

/-- The polynomial functions with integer coefficients, set.mm's `Poly ℤ`:
each is a function from ℂ to ℂ that some polynomial over ℤ gives. -/
@[expose] def integerPolynomials : Set (ℂ → ℂ) :=
  {f | ∃ P : Polynomial ℤ, ∀ x, f x = aeval x P}

open Classical in
/-- The degree of a function, set.mm's `deg`: of the polynomial over ℂ that
gives it, which is one as ℂ is infinite, and 0 where none does. -/
@[expose] noncomputable def degree (f : ℂ → ℂ) : ℕ :=
  if h : ∃ P : Polynomial ℂ, ∀ x, f x = P.eval x then (Classical.choose h).natDegree else 0

theorem aeval_eq_eval_map (P : Polynomial ℤ) (x : ℂ) :
    aeval x P = (P.map (Int.castRingHom ℂ)).eval x := by
  rw [aeval_def, eval_map]; rfl

/-- The degree of the function a polynomial over ℤ gives is that
polynomial's. -/
theorem degree_of {f : ℂ → ℂ} {P : Polynomial ℤ} (hf : ∀ x, f x = aeval x P) :
    degree f = P.natDegree := by
  have h : ∃ Q : Polynomial ℂ, ∀ x, f x = Q.eval x :=
    ⟨P.map (Int.castRingHom ℂ), fun x => by rw [hf, aeval_eq_eval_map]⟩
  unfold degree
  rw [dif_pos h]
  have e : Classical.choose h = P.map (Int.castRingHom ℂ) :=
    Polynomial.funext fun x => by rw [← Classical.choose_spec h x, hf, aeval_eq_eval_map]
  rw [e, natDegree_map_eq_of_injective (RingHom.injective_int _)]

/-- At a real, a polynomial over ℤ takes the value of the same polynomial
over ℝ. -/
theorem aeval_real (P : Polynomial ℤ) (x : ℝ) :
    aeval (x : ℂ) P = (((P.map (Int.castRingHom ℝ)).eval x : ℝ) : ℂ) := by
  have h := Polynomial.aeval_algebraMap_apply ℂ x P
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def]
  exact h

/-- `mun:stdlib/polynomials/integer-polynomial-real`. -/
theorem integer_polynomial_real (F : ℂ → ℂ) (h1 : F ∈ integerPolynomials) (x : ℝ) :
    ∃ m : ℝ, (m : ℂ) = F x := by
  obtain ⟨P, hP⟩ := h1
  exact ⟨_, (hP x ▸ aeval_real P x).symm⟩

/-- `thm:stdlib/polynomials/integer-polynomial-at-a-fraction`: each term
a·(p/q)^k times q^deg(F) is the integer a·p^k·q^(deg(F) − k). -/
theorem integer_polynomial_at_a_fraction (F : ℂ → ℂ) (h1 : F ∈ integerPolynomials)
    (p q : ℤ) (hq : 0 < q) :
    ∃ m : ℤ, (m : ℂ) = (q : ℂ) ^ degree F * F ((p : ℂ) / q) := by
  obtain ⟨P, hP⟩ := h1
  rw [degree_of hP, hP]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * p ^ i * q ^ (P.natDegree - i), ?_⟩
  rw [aeval_eq_sum_range, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Algebra.smul_def, div_pow]
  simp only [algebraMap_int_eq, eq_intCast]
  field_simp
  rw [mul_assoc (_ * _), ← pow_add, Nat.sub_add_cancel hi]

/-- A function on the reals that agrees with an integer polynomial is a
polynomial over ℝ. -/
theorem real_polynomial (F : ℂ → ℂ) (h1 : F ∈ integerPolynomials) (f : ℝ → ℝ)
    (h2 : ∀ x : ℝ, (f x : ℂ) = F x) : ∃ Q : Polynomial ℝ, f = fun x => Q.eval x := by
  obtain ⟨P, hP⟩ := h1
  refine ⟨P.map (Int.castRingHom ℝ), funext fun x => ?_⟩
  apply Complex.ofReal_injective
  rw [h2 x, hP, aeval_real]

/-- `thm:stdlib/polynomials/polynomial-on-the-reals`, its sentences
together: f, a polynomial over ℝ, is continuous and differentiable, and so
is continuous its derivative, the derivative polynomial's function. -/
theorem polynomial_on_the_reals (F : ℂ → ℂ) (h1 : F ∈ integerPolynomials) (f : ℝ → ℝ)
    (h2 : ∀ x : ℝ, (f x : ℂ) = F x) :
    Continuous f ∧ Differentiable ℝ f ∧ Continuous (deriv f) := by
  obtain ⟨Q, rfl⟩ := real_polynomial F h1 f h2
  refine ⟨Q.continuous, Q.differentiable, ?_⟩
  have : deriv (fun x => Q.eval x) = fun x => (derivative Q).eval x :=
    funext fun _ => Q.deriv
  rw [this]; exact (derivative Q).continuous

/-- `thm:stdlib/polynomials/roots-isolated`: a polynomial of positive
degree has finitely many roots, so one root has a neighbourhood with no
other. -/
theorem roots_isolated (F : ℂ → ℂ) (h1 : F ∈ integerPolynomials) (hdeg : 0 < degree F)
    (α : ℝ) : ∃ δ : ℝ, δ > 0 ∧ ∀ r : ℝ, (|α - r| ≤ δ ∧ F r = 0) → r = α := by
  obtain ⟨P, hP⟩ := h1
  rw [degree_of hP] at hdeg
  have hP0 : P.map (Int.castRingHom ℝ) ≠ 0 := by
    intro h
    rw [Polynomial.map_eq_zero_iff (RingHom.injective_int _)] at h
    simp [h] at hdeg
  set Q := P.map (Int.castRingHom ℝ)
  have hroot : ∀ r : ℝ, F r = 0 → Q.IsRoot r := by
    intro r hr
    have : ((Q.eval r : ℝ) : ℂ) = F r := by rw [hP, aeval_real]
    rw [hr] at this
    exact_mod_cast this
  set S := (Q.roots.toFinset.erase α)
  by_cases hS : S.Nonempty
  · refine ⟨(S.image fun r => |α - r|).min' (hS.image _) / 2, ?_, ?_⟩
    · have : 0 < (S.image fun r => |α - r|).min' (hS.image _) := by
        rw [Finset.lt_min'_iff]
        intro y hy
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
        exact abs_pos.mpr (sub_ne_zero.mpr (Finset.ne_of_mem_erase hr).symm)
      linarith
    · rintro r ⟨hd, hr⟩
      by_contra hne
      have hrS : r ∈ S := Finset.mem_erase.mpr ⟨hne, Multiset.mem_toFinset.mpr
        ((mem_roots hP0).mpr (hroot r hr))⟩
      have hle := Finset.min'_le _ _ (Finset.mem_image_of_mem (fun r => |α - r|) hrS)
      have hpos : 0 < |α - r| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
      linarith
  · refine ⟨1, one_pos, ?_⟩
    rintro r ⟨-, hr⟩
    by_contra hne
    exact hS ⟨r, Finset.mem_erase.mpr ⟨hne, Multiset.mem_toFinset.mpr
      ((mem_roots hP0).mpr (hroot r hr))⟩⟩

/-- `thm:stdlib/polynomials/algebraic-root`: an algebraic number is a root
of a polynomial over ℤ other than 0, which has a root, so is of positive
degree. -/
theorem algebraic_root (α : ℂ) (h : IsAlgebraic ℤ α) :
    ∃ F : ℂ → ℂ, F ∈ integerPolynomials ∧ 0 < degree F ∧ F α = 0 := by
  obtain ⟨P, hP0, hPα⟩ := h
  refine ⟨fun x => aeval x P, ⟨P, fun _ => rfl⟩, ?_, hPα⟩
  rw [degree_of (fun _ => rfl)]
  by_contra hd
  push Not at hd
  rw [Nat.le_zero, natDegree_eq_zero] at hd
  obtain ⟨c, rfl⟩ := hd
  have : (c : ℂ) = 0 := by simpa using hPα
  have hc : c = 0 := by exact_mod_cast this
  exact hP0 (by rw [hc, map_zero])

end Integer

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
