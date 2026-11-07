module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/a-theorem-cited-at-a-raised-power.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.AnImplicationUsedAsAConditional

theorem an_implication_used_as_a_conditional (x : ℝ) (hH2 : x > 1 → x > 0) (hH3 : x > 1) :
    x > 0 := by
  -- 1. mun:modus-ponens, from H2, H3
  have s1 : x > 0 := by first | linarith [(Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := 1 < x) (Q := 0 < x) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := 1 < x) (Q := 0 < x) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := 1 < x) (Q := 0 < x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := 1 < x) (Q := 0 < x) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.AnImplicationUsedAsAConditional
