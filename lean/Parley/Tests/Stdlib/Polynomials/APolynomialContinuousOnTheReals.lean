module

public import Polynomials
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Polynomials

/-! Written from tests/stdlib/polynomials.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Polynomials.APolynomialContinuousOnTheReals

theorem a_polynomial_continuous_on_the_reals (G : ℂ → ℂ) (hH2 : G ∈ LeanBridges.Polynomials.integerPolynomials) (g : ℝ → ℝ) (hH4 : ∀ x : ℝ, (g x : ℂ) = G (x : ℂ)) :
    ContinuousOn g (Set.univ : Set ℝ) := by
  -- 1. thm:polynomial-on-the-reals F := G, f := g, from H2, H4
  exact (Parley.Items.Stdlib.Polynomials.thm_polynomial_on_the_reals_1 (F := G) (f := g) hH2 hH4)

end Parley.Tests.Stdlib.Polynomials.APolynomialContinuousOnTheReals
