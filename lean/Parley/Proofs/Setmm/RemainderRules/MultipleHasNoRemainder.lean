module

public import AlgebraTactics
public import ArithTactics
public import Divisibility
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall
public import Parley.Proofs.Setmm.RemainderFacts.RemainderShifts

/-! Written from proofs/setmm/remainder-rules.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderRules.MultipleHasNoRemainder

theorem multiple_has_no_remainder (A : ℤ) (M : ℝ) (hH3 : M > 0) :
    LeanBridges.Divisibility.mod ((A : ℝ) * M) M = 0 := by
  -- 1. algebra
  have s1 : (A : ℝ) * M = M * (A : ℝ) := by parley_ring
  -- 2. calculation
  have r16_1 : (0 : ℤ) ≤ 0 := by parley_arith
  calc LeanBridges.Divisibility.mod ((A : ℝ) * M) M = LeanBridges.Divisibility.mod (M * (A : ℝ)) M := by (have h := congrArg (fun t : ℝ => LeanBridges.Divisibility.mod t M) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = LeanBridges.Divisibility.mod (0 : ℝ) M := by simpa only [zero_add] using (Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := (0 : ℝ)) (M := M) (by parley_side) (K := A))
    _ = 0 := by exact (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := (0 : ℝ)) (B := M) (by parley_side) (by parley_side) hH3)

end Parley.Proofs.Setmm.RemainderRules.MultipleHasNoRemainder
