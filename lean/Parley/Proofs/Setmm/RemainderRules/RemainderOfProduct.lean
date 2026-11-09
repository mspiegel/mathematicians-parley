module

public import Divisibility
public import InstanceTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Setmm.RemainderFacts.RemainderShifts

/-! Written from proofs/setmm/remainder-rules.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderRules.RemainderOfProduct

theorem remainder_of_product (A : ℝ) (B : ℤ) (M : ℝ) (hH4 : M > 0) :
    LeanBridges.Divisibility.mod (LeanBridges.Divisibility.mod A M * (B : ℝ)) M = LeanBridges.Divisibility.mod (A * (B : ℝ)) M := by
  -- 1. inequalities
  have s1 : M ≠ 0 := by parley_side
  set q : ℤ := ⌊A / M⌋ with hD1
  have hD1_kind : True := by trivial
  -- 2. mun:mod-value a := A, b := M, from D1, H4
  have s2 : LeanBridges.Divisibility.mod A M = A - M * (q : ℝ) := by
    try simp only [hD1] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := M) hH4)
  -- 3. algebra, from 2
  have s3 : LeanBridges.Divisibility.mod A M * (B : ℝ) = A * (B : ℝ) + M * -((q : ℝ) * (B : ℝ)) := by linear_combination (norm := parley_norm) ((B : ℝ)) * s2
  -- 4. calculation
  calc LeanBridges.Divisibility.mod (LeanBridges.Divisibility.mod A M * (B : ℝ)) M = LeanBridges.Divisibility.mod (A * (B : ℝ) + M * -((q : ℝ) * (B : ℝ))) M := by (have h := congrArg (fun t : ℝ => LeanBridges.Divisibility.mod t M) s3; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = LeanBridges.Divisibility.mod (A * (B : ℝ)) M := by
        have hI : LeanBridges.Divisibility.mod (A * (B : ℝ) + M * -((q : ℝ) * (B : ℝ))) M = LeanBridges.Divisibility.mod (A * (B : ℝ)) M := by parley_instance ((Parley.Proofs.Setmm.RemainderFacts.RemainderShifts.remainder_shifts (X := A * (B : ℝ)) (M := M) (by parley_side) (K := -(q * B))))
        exact hI

end Parley.Proofs.Setmm.RemainderRules.RemainderOfProduct
