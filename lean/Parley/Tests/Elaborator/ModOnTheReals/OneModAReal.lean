module

public import ArithTactics
public import Divisibility
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/mod-on-the-reals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ModOnTheReals.OneModAReal

theorem one_mod_a_real (N : ℝ) (hH2 : 1 < N) :
    LeanBridges.Divisibility.mod (1 : ℝ) N = 1 := by
  -- 1. mun:mod-below a := 1, b := N, from H2
  have r11_1 : (0 : ℤ) ≤ 1 := by parley_arith
  exact (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := (1 : ℝ)) (b := N) (by norm_num) hH2)

end Parley.Tests.Elaborator.ModOnTheReals.OneModAReal
