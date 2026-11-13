module

public import AlgebraTactics
public import ArithTactics
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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineCitingATheorem

theorem a_chain_line_citing_a_theorem (a : ℝ) (b : ℝ) (hH3 : a * 2 = b * 2) :
    a = b + 0 := by
  -- 1. calculation
  have r60_1 : (2 : ℤ) ≠ 0 := by parley_arith
  calc a = b := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := a) (b := b) (c := (2 : ℝ)) hH3 (by norm_num))
    _ = b + 0 := by parley_ring

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineCitingATheorem
