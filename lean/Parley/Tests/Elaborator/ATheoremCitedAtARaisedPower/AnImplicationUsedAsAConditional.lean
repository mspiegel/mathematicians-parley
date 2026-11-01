module

public import Parley.Items.Stdlib.Reasoning
public import Parley.Library

/-! Written from tests/elaborator/a-theorem-cited-at-a-raised-power.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.AnImplicationUsedAsAConditional

theorem an_implication_used_as_a_conditional (x : ℝ) (hH2 : x > 1 → x > 0) (hH3 : x > 1) :
    x > 0 := by
  -- 1. mun:modus-ponens, from H2, H3
  have s1 : x > 0 := by linarith [(Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := 1 < x) (Q := 0 < x) (by parley_side) (by parley_side))]
  all_goals parley_side

end Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.AnImplicationUsedAsAConditional
