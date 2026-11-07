module

public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
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
  have s1 : a + b ≥ 0 ∨ a + b < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a + b)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a + b))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a + b)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a + b)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := a + b)); parley_side)
  -- 2. cases, from 1
  have s2 : abs (a + b) ≤ abs a + abs b := by
    rcases s1 with hC1 | hC2
    · skip
      -- 2.1. thm:sum-nonneg-bounded, from C1
      have s2_1 : abs (a + b) ≤ abs a + abs b := by first | linarith [(Parley.Tests.Docs.Syntax.SumNonnegBounded.sum_nonneg_bounded (a := a) (b := b) hC1)] | (have h := (Parley.Tests.Docs.Syntax.SumNonnegBounded.sum_nonneg_bounded (a := a) (b := b) hC1); push_cast at h; linarith) | exact_mod_cast (Parley.Tests.Docs.Syntax.SumNonnegBounded.sum_nonneg_bounded (a := a) (b := b) hC1) | (have h := (Parley.Tests.Docs.Syntax.SumNonnegBounded.sum_nonneg_bounded (a := a) (b := b) hC1); parley_side)
      all_goals parley_side
    · skip
      -- 2.2. thm:sum-neg-bounded, from C2
      have s2_2 : abs (a + b) ≤ abs a + abs b := by first | linarith [(Parley.Tests.Docs.Syntax.SumNegBounded.sum_neg_bounded (a := a) (b := b) hC2)] | (have h := (Parley.Tests.Docs.Syntax.SumNegBounded.sum_neg_bounded (a := a) (b := b) hC2); push_cast at h; linarith) | exact_mod_cast (Parley.Tests.Docs.Syntax.SumNegBounded.sum_neg_bounded (a := a) (b := b) hC2) | (have h := (Parley.Tests.Docs.Syntax.SumNegBounded.sum_neg_bounded (a := a) (b := b) hC2); parley_side)
      all_goals parley_side
  all_goals exact s2

end Parley.Tests.Docs.Syntax.TriangleByCases
