module

public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmSubstituted

theorem a_logarithm_substituted (a : ℝ) (hH2 : a = Real.log (8 : ℝ)) :
    a = 3 * Real.log (2 : ℝ) := by
  -- 1. substitute ln(8) = 3·ln(2) (real arithmetic) into H2
  have s1 : a = 3 * Real.log (2 : ℝ) := by parley_subst_at (show Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) by parley_real) hH2
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmSubstituted
