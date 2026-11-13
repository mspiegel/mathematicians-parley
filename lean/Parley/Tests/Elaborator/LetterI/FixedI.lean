module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/letter-i.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LetterI.FixedI

theorem fixed_i (i : ℤ) (hH1 : 0 < i) :
    i ≥ 1 := by
  -- 1. inequalities, from H1
  linarith only [hH1]

end Parley.Tests.Elaborator.LetterI.FixedI
