module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/sides-alike-but-for-spelling.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SidesAlikeButForSpelling.AtMostItselfSpeltOtherwise

theorem at_most_itself_spelt_otherwise (A : ℝ) (B : ℝ) :
    B + (A - B) ≤ A := by
  -- 1. inequalities
  linarith

end Parley.Tests.Elaborator.SidesAlikeButForSpelling.AtMostItselfSpeltOtherwise
