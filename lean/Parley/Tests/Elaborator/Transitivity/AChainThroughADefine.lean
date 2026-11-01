module

public import Parley.Library

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainThroughADefine

theorem a_chain_through_a_define (a : ℝ) (b : ℝ) (c : ℝ) (H4 : a + 1 ≤ b) (H5 : b < c) :
    a + 1 < c := by
  set e : ℝ := a + 1 with D1
  -- 1. transitivity, from D1, H4, H5
  have s1 : e < c := by parley_side
  -- 2. substitute e = a + 1 (D1) into line 1
  have s2 : a + 1 < c := by parley_subst_at D1 s1
  parley_side

end Parley.Tests.Elaborator.Transitivity.AChainThroughADefine
