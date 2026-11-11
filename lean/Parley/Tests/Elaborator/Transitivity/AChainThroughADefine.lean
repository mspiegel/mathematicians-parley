module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainThroughADefine

theorem a_chain_through_a_define (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a + 1 ≤ b) (hH5 : b < c) :
    a + 1 < c := by
  set e : ℝ := a + 1 with hD1
  have hD1_kind : True := by parley_side
  -- 1. transitivity, from D1, H4, H5
  have s1 : e < c := by parley_order
  -- 2. substitute e = a + 1 (D1) into line 1
  (have h := Eq.subst (motive := (fun t : ℝ => t < c)) hD1 s1; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Tests.Elaborator.Transitivity.AChainThroughADefine
