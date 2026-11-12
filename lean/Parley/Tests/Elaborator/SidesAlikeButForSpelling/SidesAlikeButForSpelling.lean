module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/sides-alike-but-for-spelling.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SidesAlikeButForSpelling.SidesAlikeButForSpelling

theorem sides_alike_but_for_spelling (A : ℝ) (B : ℝ) :
    ¬ A < B + (A - B) := by
  -- 1. inequalities
  linarith

end Parley.Tests.Elaborator.SidesAlikeButForSpelling.SidesAlikeButForSpelling
