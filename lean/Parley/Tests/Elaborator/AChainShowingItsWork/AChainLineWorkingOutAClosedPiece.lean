module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineWorkingOutAClosedPiece

theorem a_chain_line_working_out_a_closed_piece (x : ℝ) :
    x * Real.sqrt (4 : ℝ) = 2 * x := by
  -- 1. calculation
  calc x * Real.sqrt (4 : ℝ) = x * 2 := by
        have hv1 : Real.sqrt (4 : ℝ) = 2 := by rw [congrArg Real.sqrt (show (4 : ℝ) = 2 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
        linear_combination (x) * hv1
    _ = 2 * x := by ring1

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineWorkingOutAClosedPiece
