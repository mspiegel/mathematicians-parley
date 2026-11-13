module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/a-theorem-cited-at-a-raised-power.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.AnImplicationUsedAsAConditional

theorem an_implication_used_as_a_conditional (x : ℝ) (hH2 : x > 1 → x > 0) (hH3 : x > 1) :
    x > 0 := by
  -- 1. mun:modus-ponens, from H2, H3
  exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := 1 < x) (Q := 0 < x) hH2 hH3)

end Parley.Tests.Elaborator.ATheoremCitedAtARaisedPower.AnImplicationUsedAsAConditional
