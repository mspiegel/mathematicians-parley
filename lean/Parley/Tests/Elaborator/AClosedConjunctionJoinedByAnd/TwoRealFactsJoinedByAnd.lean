module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

/-! Written from tests/elaborator/a-closed-conjunction-joined-by-and.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AClosedConjunctionJoinedByAnd.TwoRealFactsJoinedByAnd

theorem two_real_facts_joined_by_and :
    (Real.sqrt (4 : ℝ) = 2 ∧ Real.pi > 3) := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (4 : ℝ) = 2 ∧ Real.pi > 3 := by
    have hc1 : Real.sqrt (4 : ℝ) = 2 := by
      have hv1 : Real.sqrt (4 : ℝ) = 2 := by rw [congrArg Real.sqrt (show (4 : ℝ) = 2 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
      linear_combination hv1
    have hc2 : Real.pi > 3 := by
      have hf1 : 3 < Real.pi := Real.pi_gt_three
      have hf2 : Real.pi < 4 := Real.pi_lt_four
      linarith only [hf1, hf2]
    exact ⟨hc1, hc2⟩
  exact ⟨(s1).1, (s1).2⟩

end Parley.Tests.Elaborator.AClosedConjunctionJoinedByAnd.TwoRealFactsJoinedByAnd
