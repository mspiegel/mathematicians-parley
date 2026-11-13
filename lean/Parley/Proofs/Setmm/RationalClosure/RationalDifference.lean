module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Proofs.Setmm.RationalClosure.RationalSum

/-! Written from proofs/setmm/rational-closure.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RationalClosure.RationalDifference

theorem rational_difference (A : ℚ) (B : ℚ) :
    True := by
  -- 1. thm:rational-sum B := −B
  -- 2. substitute
  exact trivial

end Parley.Proofs.Setmm.RationalClosure.RationalDifference
