module

public import Polynomials
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Polynomials

/-! Written from tests/stdlib/polynomials.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Polynomials.ARootIsolated

theorem a_root_isolated (G : ℂ → ℂ) (hH2 : G ∈ LeanBridges.Polynomials.integerPolynomials) (n : ℤ) (hH3 : 0 < n) (hH4 : (LeanBridges.Polynomials.degree G : ℤ) = n) (β : ℝ) (hH6 : G (β : ℂ) = 0) :
    (∃ δ : ℝ, δ > 0 ∧ (∀ r : ℝ, abs (β - r) ≤ δ ∧ G (r : ℂ) = 0 → r = β)) := by
  -- 1. thm:roots-isolated F := G, N := n, α := β, from H2, H4, H6
  exact (Parley.Items.Stdlib.Polynomials.thm_roots_isolated (F := G) hH2 (N := n) hH3 hH4 (α := β) hH6)

end Parley.Tests.Stdlib.Polynomials.ARootIsolated
