module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AChainPairInARequiresLine

theorem a_chain_pair_in_a_requires_line (x : ℝ) (y : ℝ) (hH3 : x ^ 2 = y ∧ y = 0) :
    x = 0 := by
  -- 1. mun:square-zero
  have r40_1 : x ^ 2 = 0 := by exact Eq.trans (hH3.1) hH3.2
  exact (Parley.Items.Stdlib.Numbers.mun_square_zero (x := x) r40_1)

end Parley.Tests.Elaborator.ReadingEquations.AChainPairInARequiresLine
