module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.IffFromRight

theorem iff_from_right (x : ℝ) (hH2 : x = 0 ↔ x ^ 2 = 0) (hH3 : x ^ 2 = 0) :
    x = 0 := by
  -- 1. mun:reasoning-iff-from-right, from H2, H3
  exact (Parley.Items.Stdlib.Reasoning.mun_iff_from_right (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3)

end Parley.Tests.Stdlib.Reasoning.IffFromRight
