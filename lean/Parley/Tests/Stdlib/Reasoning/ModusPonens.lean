module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.ModusPonens

theorem modus_ponens (x : ℝ) (hH2 : x = 0 → x ≤ 0) (hH3 : x = 0) :
    x ≤ 0 := by
  -- 1. mun:reasoning-modus-ponens, from H2, H3
  exact (Parley.Items.Stdlib.Reasoning.mun_modus_ponens (P := x = 0) (Q := x ≤ 0) hH2 hH3)

end Parley.Tests.Stdlib.Reasoning.ModusPonens
