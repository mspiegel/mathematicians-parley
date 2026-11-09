module

public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Tests.Docs.Syntax.SumNegBounded
public import Parley.Tests.Docs.Syntax.SumNonnegBounded

/-! Written from tests/docs/syntax.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Syntax.TriangleByCases

theorem triangle_by_cases (a : ℝ) (b : ℝ) :
    abs (a + b) ≤ abs a + abs b := by
  -- 1. mun:nonneg-or-neg x := a + b
  have s1 : a + b ≥ 0 ∨ a + b < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a + b))
  -- 2. cases, from 1
  rcases s1 with hC1 | hC2
  · skip
    -- 2.1. thm:sum-nonneg-bounded, from C1
    exact (Parley.Tests.Docs.Syntax.SumNonnegBounded.sum_nonneg_bounded (a := a) (b := b) (by parley_side))
  · skip
    -- 2.2. thm:sum-neg-bounded, from C2
    exact (Parley.Tests.Docs.Syntax.SumNegBounded.sum_neg_bounded (a := a) (b := b) hC2)

end Parley.Tests.Docs.Syntax.TriangleByCases
