module

public import Divisibility
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall
public import Parley.Proofs.Setmm.RemainderFacts.RemainderShifts

/-! Written from proofs/setmm/remainder-rules.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderRules.MultipleHasNoRemainder

theorem multiple_has_no_remainder (A : ℤ) (M : ℝ) (hH3 : M > 0) :
    LeanBridges.Divisibility.mod ((A : ℝ) * M) M = 0 := by
  -- 1. algebra
  have s1 : (A : ℝ) * M = M * (A : ℝ) := by ring1
  -- 2. calculation
  have r16_1 : (0 : ℤ) ≤ 0 := by norm_num
  calc LeanBridges.Divisibility.mod ((A : ℝ) * M) M = LeanBridges.Divisibility.mod (M * (A : ℝ)) M := congrArg (fun t : ℝ => LeanBridges.Divisibility.mod t M) s1
    _ = LeanBridges.Divisibility.mod (0 : ℝ) M := by simpa only [zero_add] using (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) hH3 (K := A))
    _ = 0 := by exact (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (0 : ℝ)) (B := M) hH3 (by norm_num) hH3)

end Parley.Proofs.Setmm.RemainderRules.MultipleHasNoRemainder
