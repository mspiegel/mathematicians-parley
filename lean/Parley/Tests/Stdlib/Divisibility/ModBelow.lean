module

public import Divisibility
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.ModBelow

theorem mod_below (a : ℝ) (b : ℝ) (hH3 : 0 ≤ a) (hH4 : a < b) :
    LeanBridges.Divisibility.mod a b = a := by
  -- 1. mun:divisibility-mod-below, from H3, H4
  exact (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := a) (b := b) hH3 hH4)

end Parley.Tests.Stdlib.Divisibility.ModBelow
