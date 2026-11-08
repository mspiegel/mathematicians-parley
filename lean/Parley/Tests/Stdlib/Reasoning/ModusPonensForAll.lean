module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.ModusPonensForAll

theorem modus_ponens_for_all (n : ℤ) (hH1 : 0 < n) (hH2 : n ≤ 3 → (∀ x : ℝ, x ≠ 0 → x ^ 2 > 0)) (hH3 : n ≤ 3) :
    (∀ x : ℝ, x ≠ 0 → x ^ 2 > 0) := by
  -- 1. mun:reasoning-modus-ponens, from H2, H3
  exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := n ≤ 3) (Q := ∀ x : ℝ, x ≠ 0 → 0 < x ^ 2) hH2 hH3)

end Parley.Tests.Stdlib.Reasoning.ModusPonensForAll
