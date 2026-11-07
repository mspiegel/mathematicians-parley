module

public import Polynomials
public import Tactics
public import Batteries.Logic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Rat
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
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

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
