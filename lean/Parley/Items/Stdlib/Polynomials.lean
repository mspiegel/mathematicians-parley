module

public import Counting
public import Polynomials
public import Batteries.Logic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Order.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

/-! Written from corpus/stdlib/polynomials.records by parley build lean. -/

public section

namespace Parley.Items.Stdlib.Polynomials

theorem thm_remainder (p : ℂ → ℂ) (h1 : p ∈ LeanBridges.Polynomials.polynomials) (a : ℂ) :
    ∃ q : ℂ → ℂ, q ∈ LeanBridges.Polynomials.polynomials ∧ (∀ x : ℂ, p x = (x - a) * q x + p a) :=
  LeanBridges.Polynomials.remainder p h1 a

theorem mun_polynomial_value (p : ℂ → ℂ) (h1 : p ∈ LeanBridges.Polynomials.polynomials) (x : ℂ) :
    True :=
  trivial

theorem def_B (n : ℤ) (h1 : 0 ≤ n) (x : ℂ) :
    Polynomial.aeval x (Polynomial.bernoulli n.toNat) = x ^ n.toNat - (∑ k ∈ Finset.Icc (0 : ℤ) (n - 1), ((LeanBridges.Counting.choose n k : ℂ) * (Polynomial.aeval x (Polynomial.bernoulli k.toNat) / ((n : ℂ) - (k : ℂ) + 1)) : ℂ)) :=
  LeanBridges.Polynomials.B n h1 x

theorem mun_bernoulli_complex (n : ℤ) (h1 : 0 ≤ n) (x : ℂ) :
    True :=
  by trivial

theorem thm_bernoulli_difference (n : ℤ) (h1 : 0 < n) (x : ℂ) :
    Polynomial.aeval (x + 1) (Polynomial.bernoulli n.toNat) - Polynomial.aeval x (Polynomial.bernoulli n.toNat) = (n : ℂ) * x ^ (n - 1) :=
  by lift n to ℕ using h1.le; simp only [Int.toNat_natCast]; have h := congr_arg (Polynomial.aeval x) (Polynomial.bernoulli_comp_one_add_X n); simp only [Polynomial.aeval_comp, map_add, nsmul_eq_mul, map_mul, map_natCast, map_pow, Polynomial.aeval_X, map_one] at h; push_cast; rw [add_comm x 1, h, (show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by omega), zpow_natCast]; ring

theorem thm_algebraic_root (α : ℂ) (h2 : IsAlgebraic ℤ α) :
    ∃ F : ℂ → ℂ, Set.MapsTo F (Set.univ : Set ℂ) (Set.univ : Set ℂ) ∧ ((F ∈ LeanBridges.Polynomials.integerPolynomials ∧ 0 < (LeanBridges.Polynomials.degree F : ℤ)) ∧ F α = 0) :=
  by obtain ⟨F, hF, hd, hα⟩ := LeanBridges.Polynomials.algebraic_root α h2; exact ⟨F, Set.mapsTo_univ _ _, ⟨hF, by exact_mod_cast hd⟩, hα⟩

theorem def_transcendental (α : ℂ) :
    Transcendental ℤ α ↔ ¬ IsAlgebraic ℤ α :=
  by (aesop)

theorem thm_integer_polynomial_at_a_fraction (F : ℂ → ℂ) (h1 : F ∈ LeanBridges.Polynomials.integerPolynomials) (p : ℤ) (q : ℤ) (h3 : 0 < q) :
    ∃ m : ℤ, (m : ℂ) = (q : ℂ) ^ LeanBridges.Polynomials.degree F * F ((p : ℂ) / (q : ℂ)) :=
  LeanBridges.Polynomials.integer_polynomial_at_a_fraction F h1 p q h3

theorem mun_integer_polynomial_real (F : ℂ → ℂ) (h1 : F ∈ LeanBridges.Polynomials.integerPolynomials) (x : ℝ) :
    ∃ m : ℝ, (m : ℂ) = F (x : ℂ) :=
  LeanBridges.Polynomials.integer_polynomial_real F h1 x

theorem thm_roots_isolated (F : ℂ → ℂ) (h1 : F ∈ LeanBridges.Polynomials.integerPolynomials) (N : ℤ) (h2 : 0 < N) (h3 : (LeanBridges.Polynomials.degree F : ℤ) = N) (α : ℝ) (h5 : F (α : ℂ) = 0) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ r : ℝ, abs (α - r) ≤ δ ∧ F (r : ℂ) = 0 → r = α) :=
  LeanBridges.Polynomials.roots_isolated F h1 (by rw [← h3] at h2; exact_mod_cast h2) α

theorem thm_polynomial_on_the_reals_1 (F : ℂ → ℂ) (f : ℝ → ℝ) (h1 : F ∈ LeanBridges.Polynomials.integerPolynomials) (h2 : ∀ x : ℝ, (f x : ℂ) = F (x : ℂ)) :
    ContinuousOn f (Set.univ : Set ℝ) :=
  (LeanBridges.Polynomials.polynomial_on_the_reals F h1 f h2).1.continuousOn

theorem thm_polynomial_on_the_reals_2 (F : ℂ → ℂ) (f : ℝ → ℝ) (h1 : F ∈ LeanBridges.Polynomials.integerPolynomials) (h2 : ∀ x : ℝ, (f x : ℂ) = F (x : ℂ)) :
    ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ f x :=
  fun x _ => (LeanBridges.Polynomials.polynomial_on_the_reals F h1 f h2).2.1 x

theorem thm_polynomial_on_the_reals_3 (F : ℂ → ℂ) (f : ℝ → ℝ) (h1 : F ∈ LeanBridges.Polynomials.integerPolynomials) (h2 : ∀ x : ℝ, (f x : ℂ) = F (x : ℂ)) :
    True :=
  trivial

theorem thm_polynomial_on_the_reals_4 (F : ℂ → ℂ) (f : ℝ → ℝ) (h1 : F ∈ LeanBridges.Polynomials.integerPolynomials) (h2 : ∀ x : ℝ, (f x : ℂ) = F (x : ℂ)) :
    ContinuousOn (deriv f) (Set.univ : Set ℝ) :=
  (LeanBridges.Polynomials.polynomial_on_the_reals F h1 f h2).2.2.continuousOn

end Parley.Items.Stdlib.Polynomials
