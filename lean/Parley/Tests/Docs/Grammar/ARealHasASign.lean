module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.ARealHasASign

theorem a_real_has_a_sign (x : ℝ) :
    ((x < 0 ∨ x = 0) ∨ 0 < x) := by
  -- 1. axi:trichotomy
  exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := x))

end Parley.Tests.Docs.Grammar.ARealHasASign
