module

public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/letter-i.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LetterI.FixedI

theorem fixed_i (i : ℤ) (hH1 : 0 < i) :
    i ≥ 1 := by
  -- 1. inequalities, from H1
  parley_order

end Parley.Tests.Elaborator.LetterI.FixedI
