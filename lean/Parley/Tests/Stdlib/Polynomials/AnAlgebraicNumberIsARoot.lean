module

public import Polynomials
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Polynomials

/-! Written from tests/stdlib/polynomials.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Polynomials.AnAlgebraicNumberIsARoot

theorem an_algebraic_number_is_a_root (β : ℂ) (hH2 : IsAlgebraic ℤ β) :
    (∃ G : ℂ → ℂ, Set.MapsTo G (Set.univ : Set ℂ) (Set.univ : Set ℂ) ∧ ((G ∈ LeanBridges.Polynomials.integerPolynomials ∧ 0 < (LeanBridges.Polynomials.degree G : ℤ)) ∧ G β = 0)) := by
  -- 1. thm:algebraic-root α := β, from H2
  exact (Parley.Items.Stdlib.Polynomials.thm_algebraic_root (α := β) hH2)

end Parley.Tests.Stdlib.Polynomials.AnAlgebraicNumberIsARoot
