module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.IffNotFromRight

theorem iff_not_from_right (x : ℝ) (hH2 : x = 0 ↔ x ^ 2 = 0) (hH3 : x ^ 2 ≠ 0) :
    x ≠ 0 := by
  -- 1. mun:reasoning-iff-not-from-right, from H2, H3
  exact (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3)

end Parley.Tests.Stdlib.Reasoning.IffNotFromRight
