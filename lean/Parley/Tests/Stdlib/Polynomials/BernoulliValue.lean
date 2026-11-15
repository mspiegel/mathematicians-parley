module

public import Counting
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Polynomials

/-! Written from tests/stdlib/polynomials.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Polynomials.BernoulliValue

theorem bernoulli_value (n : ℤ) (hH1 : 0 ≤ n) (x : ℂ) :
    Polynomial.aeval x (Polynomial.bernoulli n.toNat) = x ^ n.toNat - (∑ k ∈ Finset.Icc (0 : ℤ) (n - 1), ((LeanBridges.Counting.choose n k : ℂ) * (Polynomial.aeval x (Polynomial.bernoulli k.toNat) / ((n : ℂ) - (k : ℂ) + 1)) : ℂ)) := by
  -- 1. def:B
  exact (Parley.Items.Stdlib.Polynomials.def_B (n := n) hH1 (x := x))

end Parley.Tests.Stdlib.Polynomials.BernoulliValue
