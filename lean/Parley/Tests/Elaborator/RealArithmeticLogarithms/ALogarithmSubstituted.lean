module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmSubstituted

theorem a_logarithm_substituted (a : ℝ) (hH2 : a = Real.log (8 : ℝ)) :
    a = 3 * Real.log (2 : ℝ) := by
  -- 1. substitute ln(8) = 3·ln(2) (real arithmetic) into H2
  have e_real : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
    have hv1 : Real.log (8 : ℝ) = ((3 : ℕ) : ℝ) * Real.log (2 : ℝ) := by rw [congrArg Real.log (show (8 : ℝ) = 2 ^ 3 by ring1), Real.log_pow 2 3]
    linear_combination hv1
  exact Eq.subst (motive := (fun t : ℝ => a = t)) e_real hH2

end Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmSubstituted
