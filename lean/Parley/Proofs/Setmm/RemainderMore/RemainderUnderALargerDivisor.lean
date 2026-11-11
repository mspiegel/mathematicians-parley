module

public import Divisibility
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Proofs.Setmm.RemainderBounds.RemainderBelowDivisor
public import Parley.Proofs.Setmm.RemainderBounds.RemainderNonnegative
public import Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall
public import Parley.Proofs.Setmm.RemainderReal.RemainderIsReal

/-! Written from proofs/setmm/remainder-more.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderMore.RemainderUnderALargerDivisor

theorem remainder_under_a_larger_divisor (A : ℝ) (B : ℝ) (C : ℝ) (hH4 : B > 0) (hH5 : C > 0) (hH6 : B ≤ C) :
    LeanBridges.Divisibility.mod (LeanBridges.Divisibility.mod A B) C = LeanBridges.Divisibility.mod A B := by
  -- 1. thm:remainder-is-real, from H4
  -- 2. thm:remainder-nonnegative, from H4
  have s2 : 0 ≤ LeanBridges.Divisibility.mod A B := by exact (Parley.Proofs.Setmm.RemainderBounds.RemainderNonnegative.remainder_nonnegative (A := A) (B := B) (by parley_side))
  -- 3. thm:remainder-below-divisor, from H4
  have s3 : LeanBridges.Divisibility.mod A B < B := by exact (Parley.Proofs.Setmm.RemainderBounds.RemainderBelowDivisor.remainder_below_divisor (A := A) (B := B) (by parley_side))
  -- 4. transitivity, from 3, H6
  have s4 : LeanBridges.Divisibility.mod A B < C := by exact lt_of_lt_of_le s3 hH6
  -- 5. thm:remainder-of-small A := A mod B, B := C, from H5, 1, 2, 4
  exact (Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall.remainder_of_small (A := LeanBridges.Divisibility.mod A B) (B := C) (by parley_side) s2 s4)

end Parley.Proofs.Setmm.RemainderMore.RemainderUnderALargerDivisor
